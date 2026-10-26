import V185TrunkScan22Chunk346

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3095606 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3095606 : Nat := 118140960795 + 3095606 * 2 ^ 59
def prefixEnd_3095606 : Nat := 4983230072969 + 3 ^ 40 * 3095606 * 2
def baseEnd_3095606 : Nat := 1059689196628080440659049

theorem tailTrace_3095606 : CollatzResearch.WordTrace tailWord_3095606 prefixEnd_3095606 1059689196628080440659049 := by
  unfold tailWord_3095606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056626651447226516184667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75270684282103749505969781 7056626651447226516184667)
  ·
    refine ⟨10584939977170839774277001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7056626651447226516184667 10584939977170839774277001)
    ·
      refine ⟨7938704982878129830707751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10584939977170839774277001 7938704982878129830707751)
      ·
        refine ⟨11908057474317194746061627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938704982878129830707751 11908057474317194746061627)
        ·
          refine ⟨17862086211475792119092441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11908057474317194746061627 17862086211475792119092441)
          ·
            refine ⟨13396564658606844089319331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17862086211475792119092441 13396564658606844089319331)
            ·
              refine ⟨20094846987910266133978997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13396564658606844089319331 20094846987910266133978997)
              ·
                refine ⟨1883891905116587450060531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20094846987910266133978997 1883891905116587450060531)
                ·
                  refine ⟨2825837857674881175090797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883891905116587450060531 2825837857674881175090797)
                  ·
                    refine ⟨1059689196628080440659049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825837857674881175090797 1059689196628080440659049)
                    ·
                      rfl

theorem cell22_3095606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3095606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095606 prefixEnd_3095606 := by exact prefixLift 3095606
  have htrace : WordTrace (prefixWord ++ tailWord_3095606) baseStart_3095606 baseEnd_3095606 := by
    simpa [prefixWord, tailWord_3095606, baseEnd_3095606] using wordTrace_append hprefix tailTrace_3095606
  have hstable : (prefixWord ++ tailWord_3095606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095606).length < 2 ^ (prefixWord ++ tailWord_3095606).sum := by decide
  have hdescent : baseEnd_3095606 < baseStart_3095606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095660 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_3095660 : Nat := 118140960795 + 3095660 * 2 ^ 59
def prefixEnd_3095660 : Nat := 4983230072969 + 3 ^ 40 * 3095660 * 2
def baseEnd_3095660 : Nat := 1059707681931642299808883

theorem tailTrace_3095660 : CollatzResearch.WordTrace tailWord_3095660 prefixEnd_3095660 1059707681931642299808883 := by
  unfold tailWord_3095660
  simp only [CollatzResearch.WordTrace]
  refine ⟨56453997982479995740710217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75271997309973327654280289 56453997982479995740710217)
  ·
    refine ⟨42340498486859996805532663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56453997982479995740710217 42340498486859996805532663)
    ·
      refine ⟨63510747730289995208298995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42340498486859996805532663 63510747730289995208298995)
      ·
        refine ⟨95266121595434992812448493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63510747730289995208298995 95266121595434992812448493)
        ·
          refine ⟨35724795598288122304668185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95266121595434992812448493 35724795598288122304668185)
          ·
            refine ⟨26793596698716091728501139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35724795598288122304668185 26793596698716091728501139)
            ·
              refine ⟨40190395048074137592751709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26793596698716091728501139 40190395048074137592751709)
              ·
                refine ⟨15071398143027801597281891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40190395048074137592751709 15071398143027801597281891)
                ·
                  refine ⟨22607097214541702395922837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15071398143027801597281891 22607097214541702395922837)
                  ·
                    refine ⟨1059707681931642299808883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22607097214541702395922837 1059707681931642299808883)
                    ·
                      rfl

theorem cell22_3095660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_3095660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095660 prefixEnd_3095660 := by exact prefixLift 3095660
  have htrace : WordTrace (prefixWord ++ tailWord_3095660) baseStart_3095660 baseEnd_3095660 := by
    simpa [prefixWord, tailWord_3095660, baseEnd_3095660] using wordTrace_append hprefix tailTrace_3095660
  have hstable : (prefixWord ++ tailWord_3095660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095660).length < 2 ^ (prefixWord ++ tailWord_3095660).sum := by decide
  have hdescent : baseEnd_3095660 < baseStart_3095660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095677 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_3095677 : Nat := 118140960795 + 3095677 * 2 ^ 59
def prefixEnd_3095677 : Nat := 4983230072969 + 3 ^ 40 * 3095677 * 2
def baseEnd_3095677 : Nat := 1059713501379059922133831

theorem tailTrace_3095677 : CollatzResearch.WordTrace tailWord_3095677 prefixEnd_3095677 1059713501379059922133831 := by
  unfold tailWord_3095677
  simp only [CollatzResearch.WordTrace]
  refine ⟨112908616005898403384789285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75272410670598935589859523 112908616005898403384789285)
  ·
    refine ⟨21170365501105950634647991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112908616005898403384789285 21170365501105950634647991)
    ·
      refine ⟨31755548251658925951971987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21170365501105950634647991 31755548251658925951971987)
      ·
        refine ⟨47633322377488388927957981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31755548251658925951971987 47633322377488388927957981)
        ·
          refine ⟨17862495891558145847984243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47633322377488388927957981 17862495891558145847984243)
          ·
            refine ⟨26793743837337218771976365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17862495891558145847984243 26793743837337218771976365)
            ·
              refine ⟨10047653939001457039491137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26793743837337218771976365 10047653939001457039491137)
              ·
                refine ⟨7535740454251092779618353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047653939001457039491137 7535740454251092779618353)
                ·
                  refine ⟨5651805340688319584713765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535740454251092779618353 5651805340688319584713765)
                  ·
                    refine ⟨1059713501379059922133831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651805340688319584713765 1059713501379059922133831)
                    ·
                      rfl

theorem cell22_3095677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_3095677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095677 prefixEnd_3095677 := by exact prefixLift 3095677
  have htrace : WordTrace (prefixWord ++ tailWord_3095677) baseStart_3095677 baseEnd_3095677 := by
    simpa [prefixWord, tailWord_3095677, baseEnd_3095677] using wordTrace_append hprefix tailTrace_3095677
  have hstable : (prefixWord ++ tailWord_3095677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095677).length < 2 ^ (prefixWord ++ tailWord_3095677).sum := by decide
  have hdescent : baseEnd_3095677 < baseStart_3095677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095681 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 4]
def baseStart_3095681 : Nat := 118140960795 + 3095681 * 2 ^ 59
def prefixEnd_3095681 : Nat := 4983230072969 + 3 ^ 40 * 3095681 * 2
def baseEnd_3095681 : Nat := 353238290220268415011273

theorem tailTrace_3095681 : CollatzResearch.WordTrace tailWord_3095681 prefixEnd_3095681 353238290220268415011273 := by
  unfold tailWord_3095681
  simp only [CollatzResearch.WordTrace]
  refine ⟨112908761897883912067934897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75272507931922608045289931 112908761897883912067934897)
  ·
    refine ⟨84681571423412934050951173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112908761897883912067934897 84681571423412934050951173)
    ·
      refine ⟨15877794641889925134553345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84681571423412934050951173 15877794641889925134553345)
      ·
        refine ⟨11908345981417443850915009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15877794641889925134553345 11908345981417443850915009)
        ·
          refine ⟨8931259486063082888186257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11908345981417443850915009 8931259486063082888186257)
          ·
            refine ⟨6698444614547312166139693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8931259486063082888186257 6698444614547312166139693)
            ·
              refine ⟨2511916730455242062302385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6698444614547312166139693 2511916730455242062302385)
              ·
                refine ⟨1883937547841431546726789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2511916730455242062302385 1883937547841431546726789)
                ·
                  refine ⟨353238290220268415011273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883937547841431546726789 353238290220268415011273)
                  ·
                    rfl

theorem cell22_3095681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_3095681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095681 prefixEnd_3095681 := by exact prefixLift 3095681
  have htrace : WordTrace (prefixWord ++ tailWord_3095681) baseStart_3095681 baseEnd_3095681 := by
    simpa [prefixWord, tailWord_3095681, baseEnd_3095681] using wordTrace_append hprefix tailTrace_3095681
  have hstable : (prefixWord ++ tailWord_3095681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095681).length < 2 ^ (prefixWord ++ tailWord_3095681).sum := by decide
  have hdescent : baseEnd_3095681 < baseStart_3095681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095737 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 5]
def baseStart_3095737 : Nat := 118140960795 + 3095737 * 2 ^ 59
def prefixEnd_3095737 : Nat := 4983230072969 + 3 ^ 40 * 3095737 * 2
def baseEnd_3095737 : Nat := 353244680201746588544549

theorem tailTrace_3095737 : CollatzResearch.WordTrace tailWord_3095737 prefixEnd_3095737 353244680201746588544549 := by
  unfold tailWord_3095737
  simp only [CollatzResearch.WordTrace]
  refine ⟨112910804385681033631973465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75273869590454022421315643 112910804385681033631973465)
  ·
    refine ⟨84683103289260775223980099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112910804385681033631973465 84683103289260775223980099)
    ·
      refine ⟨127024654933891162835970149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84683103289260775223980099 127024654933891162835970149)
      ·
        refine ⟨23817122800104593031744403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127024654933891162835970149 23817122800104593031744403)
        ·
          refine ⟨35725684200156889547616605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23817122800104593031744403 35725684200156889547616605)
          ·
            refine ⟨13397131575058833580356227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35725684200156889547616605 13397131575058833580356227)
            ·
              refine ⟨20095697362588250370534341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13397131575058833580356227 20095697362588250370534341)
              ·
                refine ⟨3767943255485296944475189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20095697362588250370534341 3767943255485296944475189)
                ·
                  refine ⟨353244680201746588544549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3767943255485296944475189 353244680201746588544549)
                  ·
                    rfl

theorem cell22_3095737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_3095737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095737 prefixEnd_3095737 := by exact prefixLift 3095737
  have htrace : WordTrace (prefixWord ++ tailWord_3095737) baseStart_3095737 baseEnd_3095737 := by
    simpa [prefixWord, tailWord_3095737, baseEnd_3095737] using wordTrace_append hprefix tailTrace_3095737
  have hstable : (prefixWord ++ tailWord_3095737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095737).length < 2 ^ (prefixWord ++ tailWord_3095737).sum := by decide
  have hdescent : baseEnd_3095737 < baseStart_3095737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095767 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3095767 : Nat := 118140960795 + 3095767 * 2 ^ 59
def prefixEnd_3095767 : Nat := 4983230072969 + 3 ^ 40 * 3095767 * 2
def baseEnd_3095767 : Nat := 1059744310218329687383555

theorem tailTrace_3095767 : CollatzResearch.WordTrace tailWord_3095767 prefixEnd_3095767 1059744310218329687383555 := by
  unfold tailWord_3095767
  simp only [CollatzResearch.WordTrace]
  refine ⟨112911898575572348755565555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75274599050381565837043703 112911898575572348755565555)
  ·
    refine ⟨169367847863358523133348333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112911898575572348755565555 169367847863358523133348333)
    ·
      refine ⟨63512942948759446175005625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169367847863358523133348333 63512942948759446175005625)
      ·
        refine ⟨47634707211569584631254219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63512942948759446175005625 47634707211569584631254219)
        ·
          refine ⟨71452060817354376946881329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47634707211569584631254219 71452060817354376946881329)
          ·
            refine ⟨53589045613015782710160997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71452060817354376946881329 53589045613015782710160997)
            ·
              refine ⟨10047946052440459258155187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53589045613015782710160997 10047946052440459258155187)
              ·
                refine ⟨15071919078660688887232781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10047946052440459258155187 15071919078660688887232781)
                ·
                  refine ⟨5651969654497758332712293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15071919078660688887232781 5651969654497758332712293)
                  ·
                    refine ⟨1059744310218329687383555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651969654497758332712293 1059744310218329687383555)
                    ·
                      rfl

theorem cell22_3095767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3095767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095767 prefixEnd_3095767 := by exact prefixLift 3095767
  have htrace : WordTrace (prefixWord ++ tailWord_3095767) baseStart_3095767 baseEnd_3095767 := by
    simpa [prefixWord, tailWord_3095767, baseEnd_3095767] using wordTrace_append hprefix tailTrace_3095767
  have hstable : (prefixWord ++ tailWord_3095767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095767).length < 2 ^ (prefixWord ++ tailWord_3095767).sum := by decide
  have hdescent : baseEnd_3095767 < baseStart_3095767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095784 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_3095784 : Nat := 118140960795 + 3095784 * 2 ^ 59
def prefixEnd_3095784 : Nat := 4983230072969 + 3 ^ 40 * 3095784 * 2
def baseEnd_3095784 : Nat := 1059750129665747309708503

theorem tailTrace_3095784 : CollatzResearch.WordTrace tailWord_3095784 prefixEnd_3095784 1059750129665747309708503 := by
  unfold tailWord_3095784
  simp only [CollatzResearch.WordTrace]
  refine ⟨56456259308255380329467203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75275012411007173772622937 56456259308255380329467203)
  ·
    refine ⟨84684388962383070494200805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56456259308255380329467203 84684388962383070494200805)
    ·
      refine ⟨15878322930446825717662651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84684388962383070494200805 15878322930446825717662651)
      ·
        refine ⟨23817484395670238576493977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15878322930446825717662651 23817484395670238576493977)
        ·
          refine ⟨17863113296752678932370483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23817484395670238576493977 17863113296752678932370483)
          ·
            refine ⟨26794669945129018398555725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17863113296752678932370483 26794669945129018398555725)
            ·
              refine ⟨10048001229423381899458397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26794669945129018398555725 10048001229423381899458397)
              ·
                refine ⟨3768000461033768212296899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10048001229423381899458397 3768000461033768212296899)
                ·
                  refine ⟨5652000691550652318445349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768000461033768212296899 5652000691550652318445349)
                  ·
                    refine ⟨1059750129665747309708503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5652000691550652318445349 1059750129665747309708503)
                    ·
                      rfl

theorem cell22_3095784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_3095784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095784 prefixEnd_3095784 := by exact prefixLift 3095784
  have htrace : WordTrace (prefixWord ++ tailWord_3095784) baseStart_3095784 baseEnd_3095784 := by
    simpa [prefixWord, tailWord_3095784, baseEnd_3095784] using wordTrace_append hprefix tailTrace_3095784
  have hstable : (prefixWord ++ tailWord_3095784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095784).length < 2 ^ (prefixWord ++ tailWord_3095784).sum := by decide
  have hdescent : baseEnd_3095784 < baseStart_3095784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095865 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_3095865 : Nat := 118140960795 + 3095865 * 2 ^ 59
def prefixEnd_3095865 : Nat := 4983230072969 + 3 ^ 40 * 3095865 * 2
def baseEnd_3095865 : Nat := 1059777857621090098433255

theorem tailTrace_3095865 : CollatzResearch.WordTrace tailWord_3095865 prefixEnd_3095865 1059777857621090098433255 := by
  unfold tailWord_3095865
  simp only [CollatzResearch.WordTrace]
  refine ⟨112915472929217311492633049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75276981952811540995088699 112915472929217311492633049)
  ·
    refine ⟨84686604696912983619474787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112915472929217311492633049 84686604696912983619474787)
    ·
      refine ⟨127029907045369475429212181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84686604696912983619474787 127029907045369475429212181)
      ·
        refine ⟨5954526892751694160744321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127029907045369475429212181 5954526892751694160744321)
        ·
          refine ⟨4465895169563770620558241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954526892751694160744321 4465895169563770620558241)
          ·
            refine ⟨3349421377172827965418681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465895169563770620558241 3349421377172827965418681)
            ·
              refine ⟨2512066032879620974064011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349421377172827965418681 2512066032879620974064011)
              ·
                refine ⟨3768099049319431461096017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512066032879620974064011 3768099049319431461096017)
                ·
                  refine ⟨2826074286989573595822013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3768099049319431461096017 2826074286989573595822013)
                  ·
                    refine ⟨1059777857621090098433255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826074286989573595822013 1059777857621090098433255)
                    ·
                      rfl

theorem cell22_3095865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_3095865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095865 prefixEnd_3095865 := by exact prefixLift 3095865
  have htrace : WordTrace (prefixWord ++ tailWord_3095865) baseStart_3095865 baseEnd_3095865 := by
    simpa [prefixWord, tailWord_3095865, baseEnd_3095865] using wordTrace_append hprefix tailTrace_3095865
  have hstable : (prefixWord ++ tailWord_3095865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095865).length < 2 ^ (prefixWord ++ tailWord_3095865).sum := by decide
  have hdescent : baseEnd_3095865 < baseStart_3095865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095906 : List Nat := [3, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_3095906 : Nat := 118140960795 + 3095906 * 2 ^ 59
def prefixEnd_3095906 : Nat := 4983230072969 + 3 ^ 40 * 3095906 * 2
def baseEnd_3095906 : Nat := 353263964252993219386043

theorem tailTrace_3095906 : CollatzResearch.WordTrace tailWord_3095906 prefixEnd_3095906 353263964252993219386043 := by
  unfold tailWord_3095906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28229242080517193873718893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75277978881379183663250381 28229242080517193873718893)
  ·
    refine ⟨10585965780193947702644585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28229242080517193873718893 10585965780193947702644585)
    ·
      refine ⟨7939474335145460776983439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10585965780193947702644585 7939474335145460776983439)
      ·
        refine ⟨11909211502718191165475159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939474335145460776983439 11909211502718191165475159)
        ·
          refine ⟨17863817254077286748212739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909211502718191165475159 17863817254077286748212739)
          ·
            refine ⟨26795725881115930122319109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17863817254077286748212739 26795725881115930122319109)
            ·
              refine ⟨5024198602709236897934833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26795725881115930122319109 5024198602709236897934833)
              ·
                refine ⟨3768148952031927673451125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024198602709236897934833 3768148952031927673451125)
                ·
                  refine ⟨353263964252993219386043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3768148952031927673451125 353263964252993219386043)
                  ·
                    rfl

theorem cell22_3095906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_3095906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095906 prefixEnd_3095906 := by exact prefixLift 3095906
  have htrace : WordTrace (prefixWord ++ tailWord_3095906) baseStart_3095906 baseEnd_3095906 := by
    simpa [prefixWord, tailWord_3095906, baseEnd_3095906] using wordTrace_append hprefix tailTrace_3095906
  have hstable : (prefixWord ++ tailWord_3095906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095906).length < 2 ^ (prefixWord ++ tailWord_3095906).sum := by decide
  have hdescent : baseEnd_3095906 < baseStart_3095906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095981 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3095981 : Nat := 118140960795 + 3095981 * 2 ^ 59
def prefixEnd_3095981 : Nat := 4983230072969 + 3 ^ 40 * 3095981 * 2
def baseEnd_3095981 : Nat := 1059817566791704462532899

theorem tailTrace_3095981 : CollatzResearch.WordTrace tailWord_3095981 prefixEnd_3095981 1059817566791704462532899 := by
  unfold tailWord_3095981
  simp only [CollatzResearch.WordTrace]
  refine ⟨112919703796797063303855797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75279802531198042202570531 112919703796797063303855797)
  ·
    refine ⟨10586222230949724684736481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112919703796797063303855797 10586222230949724684736481)
    ·
      refine ⟨7939666673212293513552361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10586222230949724684736481 7939666673212293513552361)
      ·
        refine ⟨5954750004909220135164271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7939666673212293513552361 5954750004909220135164271)
        ·
          refine ⟨8932125007363830202746407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5954750004909220135164271 8932125007363830202746407)
          ·
            refine ⟨13398187511045745304119611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932125007363830202746407 13398187511045745304119611)
            ·
              refine ⟨20097281266568617956179417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13398187511045745304119611 20097281266568617956179417)
              ·
                refine ⟨15072960949926463467134563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20097281266568617956179417 15072960949926463467134563)
                ·
                  refine ⟨22609441424889695200701845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15072960949926463467134563 22609441424889695200701845)
                  ·
                    refine ⟨1059817566791704462532899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22609441424889695200701845 1059817566791704462532899)
                    ·
                      rfl

theorem cell22_3095981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3095981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095981 prefixEnd_3095981 := by exact prefixLift 3095981
  have htrace : WordTrace (prefixWord ++ tailWord_3095981) baseStart_3095981 baseEnd_3095981 := by
    simpa [prefixWord, tailWord_3095981, baseEnd_3095981] using wordTrace_append hprefix tailTrace_3095981
  have hstable : (prefixWord ++ tailWord_3095981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095981).length < 2 ^ (prefixWord ++ tailWord_3095981).sum := by decide
  have hdescent : baseEnd_3095981 < baseStart_3095981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095996 : List Nat := [2, 2, 2, 4, 2, 1, 1, 8]
def baseStart_3095996 : Nat := 118140960795 + 3095996 * 2 ^ 59
def prefixEnd_3095996 : Nat := 4983230072969 + 3 ^ 40 * 3095996 * 2
def baseEnd_3095996 : Nat := 117758077955361047045317

theorem tailTrace_3095996 : CollatzResearch.WordTrace tailWord_3095996 prefixEnd_3095996 117758077955361047045317 := by
  unfold tailWord_3095996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56460125445871360432825921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75280167261161813910434561 56460125445871360432825921)
  ·
    refine ⟨42345094084403520324619441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56460125445871360432825921 42345094084403520324619441)
    ·
      refine ⟨31758820563302640243464581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42345094084403520324619441 31758820563302640243464581)
      ·
        refine ⟨5954778855619245045649609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31758820563302640243464581 5954778855619245045649609)
        ·
          refine ⟨4466084141714433784237207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5954778855619245045649609 4466084141714433784237207)
          ·
            refine ⟨6699126212571650676355811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466084141714433784237207 6699126212571650676355811)
            ·
              refine ⟨10048689318857476014533717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699126212571650676355811 10048689318857476014533717)
              ·
                refine ⟨117758077955361047045317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10048689318857476014533717 117758077955361047045317)
                ·
                  rfl

theorem cell22_3095996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_3095996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095996 prefixEnd_3095996 := by exact prefixLift 3095996
  have htrace : WordTrace (prefixWord ++ tailWord_3095996) baseStart_3095996 baseEnd_3095996 := by
    simpa [prefixWord, tailWord_3095996, baseEnd_3095996] using wordTrace_append hprefix tailTrace_3095996
  have hstable : (prefixWord ++ tailWord_3095996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095996).length < 2 ^ (prefixWord ++ tailWord_3095996).sum := by decide
  have hdescent : baseEnd_3095996 < baseStart_3095996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096024 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_3096024 : Nat := 118140960795 + 3096024 * 2 ^ 59
def prefixEnd_3096024 : Nat := 4983230072969 + 3 ^ 40 * 3096024 * 2
def baseEnd_3096024 : Nat := 353277428856822227902589

theorem tailTrace_3096024 : CollatzResearch.WordTrace tailWord_3096024 prefixEnd_3096024 353277428856822227902589 := by
  unfold tailWord_3096024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56460636067820640823835563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75280848090427521098447417 56460636067820640823835563)
  ·
    refine ⟨84690954101730961235753345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56460636067820640823835563 84690954101730961235753345)
    ·
      refine ⟨63518215576298220926815009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84690954101730961235753345 63518215576298220926815009)
      ·
        refine ⟨47638661682223665695111257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63518215576298220926815009 47638661682223665695111257)
        ·
          refine ⟨35728996261667749271333443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47638661682223665695111257 35728996261667749271333443)
          ·
            refine ⟨53593494392501623907000165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35728996261667749271333443 53593494392501623907000165)
            ·
              refine ⟨10048780198594054482562531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53593494392501623907000165 10048780198594054482562531)
              ·
                refine ⟨15073170297891081723843797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10048780198594054482562531 15073170297891081723843797)
                ·
                  refine ⟨353277428856822227902589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15073170297891081723843797 353277428856822227902589)
                  ·
                    rfl

theorem cell22_3096024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_3096024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096024 prefixEnd_3096024 := by exact prefixLift 3096024
  have htrace : WordTrace (prefixWord ++ tailWord_3096024) baseStart_3096024 baseEnd_3096024 := by
    simpa [prefixWord, tailWord_3096024, baseEnd_3096024] using wordTrace_append hprefix tailTrace_3096024
  have hstable : (prefixWord ++ tailWord_3096024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096024).length < 2 ^ (prefixWord ++ tailWord_3096024).sum := by decide
  have hdescent : baseEnd_3096024 < baseStart_3096024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096101 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_3096101 : Nat := 118140960795 + 3096101 * 2 ^ 59
def prefixEnd_3096101 : Nat := 4983230072969 + 3 ^ 40 * 3096101 * 2
def baseEnd_3096101 : Nat := 1059858645244064149532531

theorem tailTrace_3096101 : CollatzResearch.WordTrace tailWord_3096101 prefixEnd_3096101 1059858645244064149532531 := by
  unfold tailWord_3096101
  simp only [CollatzResearch.WordTrace]
  refine ⟨112924080556362323798224157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75282720370908215865482771 112924080556362323798224157)
  ·
    refine ⟨42346530208635871424334059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112924080556362323798224157 42346530208635871424334059)
    ·
      refine ⟨63519795312953807136501089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42346530208635871424334059 63519795312953807136501089)
      ·
        refine ⟨47639846484715355352375817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63519795312953807136501089 47639846484715355352375817)
        ·
          refine ⟨35729884863536516514281863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47639846484715355352375817 35729884863536516514281863)
          ·
            refine ⟨53594827295304774771422795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35729884863536516514281863 53594827295304774771422795)
            ·
              refine ⟨80392240942957162157134193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53594827295304774771422795 80392240942957162157134193)
              ·
                refine ⟨60294180707217871617850645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80392240942957162157134193 60294180707217871617850645)
                ·
                  refine ⟨2826289720650837732086749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60294180707217871617850645 2826289720650837732086749)
                  ·
                    refine ⟨1059858645244064149532531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826289720650837732086749 1059858645244064149532531)
                    ·
                      rfl

theorem cell22_3096101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_3096101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096101 prefixEnd_3096101 := by exact prefixLift 3096101
  have htrace : WordTrace (prefixWord ++ tailWord_3096101) baseStart_3096101 baseEnd_3096101 := by
    simpa [prefixWord, tailWord_3096101, baseEnd_3096101] using wordTrace_append hprefix tailTrace_3096101
  have hstable : (prefixWord ++ tailWord_3096101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096101).length < 2 ^ (prefixWord ++ tailWord_3096101).sum := by decide
  have hdescent : baseEnd_3096101 < baseStart_3096101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096163 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 3, 3]
def baseStart_3096163 : Nat := 118140960795 + 3096163 * 2 ^ 59
def prefixEnd_3096163 : Nat := 4983230072969 + 3 ^ 40 * 3096163 * 2
def baseEnd_3096163 : Nat := 1059879869111116654482341

theorem tailTrace_3096163 : CollatzResearch.WordTrace tailWord_3096163 prefixEnd_3096163 1059879869111116654482341 := by
  unfold tailWord_3096163
  simp only [CollatzResearch.WordTrace]
  refine ⟨112926341882137708386981143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75284227921425138924654095 112926341882137708386981143)
  ·
    refine ⟨169389512823206562580471715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112926341882137708386981143 169389512823206562580471715)
    ·
      refine ⟨254084269234809843870707573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169389512823206562580471715 254084269234809843870707573)
      ·
        refine ⟨23820400240763422862878835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254084269234809843870707573 23820400240763422862878835)
        ·
          refine ⟨35730600361145134294318253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23820400240763422862878835 35730600361145134294318253)
          ·
            refine ⟨13398975135429425360369345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35730600361145134294318253 13398975135429425360369345)
            ·
              refine ⟨10049231351572069020277009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13398975135429425360369345 10049231351572069020277009)
              ·
                refine ⟨7536923513679051765207757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10049231351572069020277009 7536923513679051765207757)
                ·
                  refine ⟨2826346317629644411952909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7536923513679051765207757 2826346317629644411952909)
                  ·
                    refine ⟨1059879869111116654482341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826346317629644411952909 1059879869111116654482341)
                    ·
                      rfl

theorem cell22_3096163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 3].length) (baseStart_3096163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096163 prefixEnd_3096163 := by exact prefixLift 3096163
  have htrace : WordTrace (prefixWord ++ tailWord_3096163) baseStart_3096163 baseEnd_3096163 := by
    simpa [prefixWord, tailWord_3096163, baseEnd_3096163] using wordTrace_append hprefix tailTrace_3096163
  have hstable : (prefixWord ++ tailWord_3096163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096163).length < 2 ^ (prefixWord ++ tailWord_3096163).sum := by decide
  have hdescent : baseEnd_3096163 < baseStart_3096163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096176 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_3096176 : Nat := 118140960795 + 3096176 * 2 ^ 59
def prefixEnd_3096176 : Nat := 4983230072969 + 3 ^ 40 * 3096176 * 2
def baseEnd_3096176 : Nat := 353294773092262984635767

theorem tailTrace_3096176 : CollatzResearch.WordTrace tailWord_3096176 prefixEnd_3096176 353294773092262984635767 := by
  unfold tailWord_3096176
  simp only [CollatzResearch.WordTrace]
  refine ⟨56463408015545305803602191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75284544020727074404802921 56463408015545305803602191)
  ·
    refine ⟨84695112023317958705403287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56463408015545305803602191 84695112023317958705403287)
    ·
      refine ⟨127042668034976938058104931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84695112023317958705403287 127042668034976938058104931)
      ·
        refine ⟨190564002052465407087157397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127042668034976938058104931 190564002052465407087157397)
        ·
          refine ⟨8932687596209315957210503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190564002052465407087157397 8932687596209315957210503)
          ·
            refine ⟨13399031394313973935815755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932687596209315957210503 13399031394313973935815755)
            ·
              refine ⟨20098547091470960903723633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13399031394313973935815755 20098547091470960903723633)
              ·
                refine ⟨15073910318603220677792725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20098547091470960903723633 15073910318603220677792725)
                ·
                  refine ⟨353294773092262984635767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15073910318603220677792725 353294773092262984635767)
                  ·
                    rfl

theorem cell22_3096176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_3096176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096176 prefixEnd_3096176 := by exact prefixLift 3096176
  have htrace : WordTrace (prefixWord ++ tailWord_3096176) baseStart_3096176 baseEnd_3096176 := by
    simpa [prefixWord, tailWord_3096176, baseEnd_3096176] using wordTrace_append hprefix tailTrace_3096176
  have hstable : (prefixWord ++ tailWord_3096176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096176).length < 2 ^ (prefixWord ++ tailWord_3096176).sum := by decide
  have hdescent : baseEnd_3096176 < baseStart_3096176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096197 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_3096197 : Nat := 118140960795 + 3096197 * 2 ^ 59
def prefixEnd_3096197 : Nat := 4983230072969 + 3 ^ 40 * 3096197 * 2
def baseEnd_3096197 : Nat := 1059891508005951899132237

theorem tailTrace_3096197 : CollatzResearch.WordTrace tailWord_3096197 prefixEnd_3096197 1059891508005951899132237 := by
  unfold tailWord_3096197
  simp only [CollatzResearch.WordTrace]
  refine ⟨112927581964014532193718845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75285054642676354795812563 112927581964014532193718845)
  ·
    refine ⟨42347843236505449572644567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112927581964014532193718845 42347843236505449572644567)
    ·
      refine ⟨63521764854758174358966851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42347843236505449572644567 63521764854758174358966851)
      ·
        refine ⟨95282647282137261538450277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63521764854758174358966851 95282647282137261538450277)
        ·
          refine ⟨17865496365400736538459427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95282647282137261538450277 17865496365400736538459427)
          ·
            refine ⟨26798244548101104807689141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17865496365400736538459427 26798244548101104807689141)
            ·
              refine ⟨2512335426384478575720857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26798244548101104807689141 2512335426384478575720857)
              ·
                refine ⟨1884251569788358931790643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512335426384478575720857 1884251569788358931790643)
                ·
                  refine ⟨2826377354682538397685965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884251569788358931790643 2826377354682538397685965)
                  ·
                    refine ⟨1059891508005951899132237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826377354682538397685965 1059891508005951899132237)
                    ·
                      rfl

theorem cell22_3096197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_3096197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096197 prefixEnd_3096197 := by exact prefixLift 3096197
  have htrace : WordTrace (prefixWord ++ tailWord_3096197) baseStart_3096197 baseEnd_3096197 := by
    simpa [prefixWord, tailWord_3096197, baseEnd_3096197] using wordTrace_append hprefix tailTrace_3096197
  have hstable : (prefixWord ++ tailWord_3096197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096197).length < 2 ^ (prefixWord ++ tailWord_3096197).sum := by decide
  have hdescent : baseEnd_3096197 < baseStart_3096197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096210 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_3096210 : Nat := 118140960795 + 3096210 * 2 ^ 59
def prefixEnd_3096210 : Nat := 4983230072969 + 3 ^ 40 * 3096210 * 2
def baseEnd_3096210 : Nat := 353298652723874732852399

theorem tailTrace_3096210 : CollatzResearch.WordTrace tailWord_3096210 prefixEnd_3096210 353298652723874732852399 := by
  unfold tailWord_3096210
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232014028241858853485521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75285370741978290275961389 28232014028241858853485521)
  ·
    refine ⟨21174010521181394140114141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28232014028241858853485521 21174010521181394140114141)
    ·
      refine ⟨7940253945443022802542803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21174010521181394140114141 7940253945443022802542803)
      ·
        refine ⟨11910380918164534203814205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7940253945443022802542803 11910380918164534203814205)
        ·
          refine ⟨4466392844311700326430327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11910380918164534203814205 4466392844311700326430327)
          ·
            refine ⟨6699589266467550489645491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4466392844311700326430327 6699589266467550489645491)
            ·
              refine ⟨10049383899701325734468237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699589266467550489645491 10049383899701325734468237)
              ·
                refine ⟨3768518962387997150425589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10049383899701325734468237 3768518962387997150425589)
                ·
                  refine ⟨353298652723874732852399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3768518962387997150425589 353298652723874732852399)
                  ·
                    rfl

theorem cell22_3096210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_3096210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096210 prefixEnd_3096210 := by exact prefixLift 3096210
  have htrace : WordTrace (prefixWord ++ tailWord_3096210) baseStart_3096210 baseEnd_3096210 := by
    simpa [prefixWord, tailWord_3096210, baseEnd_3096210] using wordTrace_append hprefix tailTrace_3096210
  have hstable : (prefixWord ++ tailWord_3096210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096210).length < 2 ^ (prefixWord ++ tailWord_3096210).sum := by decide
  have hdescent : baseEnd_3096210 < baseStart_3096210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096221 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 8]
def baseStart_3096221 : Nat := 118140960795 + 3096221 * 2 ^ 59
def prefixEnd_3096221 : Nat := 4983230072969 + 3 ^ 40 * 3096221 * 2
def baseEnd_3096221 : Nat := 353299907898807945510721

theorem tailTrace_3096221 : CollatzResearch.WordTrace tailWord_3096221 prefixEnd_3096221 353299907898807945510721 := by
  unfold tailWord_3096221
  simp only [CollatzResearch.WordTrace]
  refine ⟨112928457315927584292592517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75285638210618389528395011 112928457315927584292592517)
  ·
    refine ⟨21174085746736422054861097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112928457315927584292592517 21174085746736422054861097)
    ·
      refine ⟨15880564310052316541145823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21174085746736422054861097 15880564310052316541145823)
      ·
        refine ⟨23820846465078474811718735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15880564310052316541145823 23820846465078474811718735)
        ·
          refine ⟨35731269697617712217578103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23820846465078474811718735 35731269697617712217578103)
          ·
            refine ⟨53596904546426568326367155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35731269697617712217578103 53596904546426568326367155)
            ·
              refine ⟨80395356819639852489550733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53596904546426568326367155 80395356819639852489550733)
              ·
                refine ⟨30148258807364944683581525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80395356819639852489550733 30148258807364944683581525)
                ·
                  refine ⟨353299907898807945510721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30148258807364944683581525 353299907898807945510721)
                  ·
                    rfl

theorem cell22_3096221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3096221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096221 prefixEnd_3096221 := by exact prefixLift 3096221
  have htrace : WordTrace (prefixWord ++ tailWord_3096221) baseStart_3096221 baseEnd_3096221 := by
    simpa [prefixWord, tailWord_3096221, baseEnd_3096221] using wordTrace_append hprefix tailTrace_3096221
  have hstable : (prefixWord ++ tailWord_3096221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096221).length < 2 ^ (prefixWord ++ tailWord_3096221).sum := by decide
  have hdescent : baseEnd_3096221 < baseStart_3096221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096270 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_3096270 : Nat := 118140960795 + 3096270 * 2 ^ 59
def prefixEnd_3096270 : Nat := 4983230072969 + 3 ^ 40 * 3096270 * 2
def baseEnd_3096270 : Nat := 1059916497397804042057013

theorem tailTrace_3096270 : CollatzResearch.WordTrace tailWord_3096270 prefixEnd_3096270 1059916497397804042057013 := by
  unfold tailWord_3096270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116280561593758207640783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75286829661833377107417509 14116280561593758207640783)
  ·
    refine ⟨21174420842390637311461175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116280561593758207640783 21174420842390637311461175)
    ·
      refine ⟨31761631263585955967191763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21174420842390637311461175 31761631263585955967191763)
      ·
        refine ⟨47642446895378933950787645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31761631263585955967191763 47642446895378933950787645)
        ·
          refine ⟨17865917585767100231545367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47642446895378933950787645 17865917585767100231545367)
          ·
            refine ⟨26798876378650650347318051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17865917585767100231545367 26798876378650650347318051)
            ·
              refine ⟨40198314567975975520977077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26798876378650650347318051 40198314567975975520977077)
              ·
                refine ⟨3768591990747747705091601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40198314567975975520977077 3768591990747747705091601)
                ·
                  refine ⟨2826443993060810778818701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3768591990747747705091601 2826443993060810778818701)
                  ·
                    refine ⟨1059916497397804042057013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826443993060810778818701 1059916497397804042057013)
                    ·
                      rfl

theorem cell22_3096270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_3096270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096270 prefixEnd_3096270 := by exact prefixLift 3096270
  have htrace : WordTrace (prefixWord ++ tailWord_3096270) baseStart_3096270 baseEnd_3096270 := by
    simpa [prefixWord, tailWord_3096270, baseEnd_3096270] using wordTrace_append hprefix tailTrace_3096270
  have hstable : (prefixWord ++ tailWord_3096270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096270).length < 2 ^ (prefixWord ++ tailWord_3096270).sum := by decide
  have hdescent : baseEnd_3096270 < baseStart_3096270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096366 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3096366 : Nat := 118140960795 + 3096366 * 2 ^ 59
def prefixEnd_3096366 : Nat := 4983230072969 + 3 ^ 40 * 3096366 * 2
def baseEnd_3096366 : Nat := 1059949360159691791656719

theorem tailTrace_3096366 : CollatzResearch.WordTrace tailWord_3096366 prefixEnd_3096366 1059949360159691791656719 := by
  unfold tailWord_3096366
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116718237550284257077619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75289163933601516037747301 14116718237550284257077619)
  ·
    refine ⟨21175077356325426385616429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116718237550284257077619 21175077356325426385616429)
    ·
      refine ⟨7940654008622034894606161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21175077356325426385616429 7940654008622034894606161)
      ·
        refine ⟨5955490506466526170954621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7940654008622034894606161 5955490506466526170954621)
        ·
          refine ⟨2233308939924947314107983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5955490506466526170954621 2233308939924947314107983)
          ·
            refine ⟨3349963409887420971161975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233308939924947314107983 3349963409887420971161975)
            ·
              refine ⟨5024945114831131456742963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349963409887420971161975 5024945114831131456742963)
              ·
                refine ⟨7537417672246697185114445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5024945114831131456742963 7537417672246697185114445)
                ·
                  refine ⟨2826531627092511444417917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7537417672246697185114445 2826531627092511444417917)
                  ·
                    refine ⟨1059949360159691791656719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826531627092511444417917 1059949360159691791656719)
                    ·
                      rfl

theorem cell22_3096366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3096366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096366 prefixEnd_3096366 := by exact prefixLift 3096366
  have htrace : WordTrace (prefixWord ++ tailWord_3096366) baseStart_3096366 baseEnd_3096366 := by
    simpa [prefixWord, tailWord_3096366, baseEnd_3096366] using wordTrace_append hprefix tailTrace_3096366
  have hstable : (prefixWord ++ tailWord_3096366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096366).length < 2 ^ (prefixWord ++ tailWord_3096366).sum := by decide
  have hdescent : baseEnd_3096366 < baseStart_3096366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096392 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_3096392 : Nat := 118140960795 + 3096392 * 2 ^ 59
def prefixEnd_3096392 : Nat := 4983230072969 + 3 ^ 40 * 3096392 * 2
def baseEnd_3096392 : Nat := 1059958260491036390506639

theorem tailTrace_3096392 : CollatzResearch.WordTrace tailWord_3096392 prefixEnd_3096392 1059958260491036390506639 := by
  unfold tailWord_3096392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56467347099154040248533715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75289796132205386998044953 56467347099154040248533715)
  ·
    refine ⟨84701020648731060372800573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56467347099154040248533715 84701020648731060372800573)
    ·
      refine ⟨31762882743274147639800215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84701020648731060372800573 31762882743274147639800215)
      ·
        refine ⟨47644324114911221459700323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31762882743274147639800215 47644324114911221459700323)
        ·
          refine ⟨71466486172366832189550485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47644324114911221459700323 71466486172366832189550485)
          ·
            refine ⟨3349991539329695258885179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71466486172366832189550485 3349991539329695258885179)
            ·
              refine ⟨5024987308994542888327769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349991539329695258885179 5024987308994542888327769)
              ·
                refine ⟨3768740481745907166245827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5024987308994542888327769 3768740481745907166245827)
                ·
                  refine ⟨5653110722618860749368741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768740481745907166245827 5653110722618860749368741)
                  ·
                    refine ⟨1059958260491036390506639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653110722618860749368741 1059958260491036390506639)
                    ·
                      rfl

theorem cell22_3096392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_3096392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096392 prefixEnd_3096392 := by exact prefixLift 3096392
  have htrace : WordTrace (prefixWord ++ tailWord_3096392) baseStart_3096392 baseEnd_3096392 := by
    simpa [prefixWord, tailWord_3096392, baseEnd_3096392] using wordTrace_append hprefix tailTrace_3096392
  have hstable : (prefixWord ++ tailWord_3096392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096392).length < 2 ^ (prefixWord ++ tailWord_3096392).sum := by decide
  have hdescent : baseEnd_3096392 < baseStart_3096392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096405 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3096405 : Nat := 118140960795 + 3096405 * 2 ^ 59
def prefixEnd_3096405 : Nat := 4983230072969 + 3 ^ 40 * 3096405 * 2
def baseEnd_3096405 : Nat := 1059962710656708689931599

theorem tailTrace_3096405 : CollatzResearch.WordTrace tailWord_3096405 prefixEnd_3096405 1059962710656708689931599 := by
  unfold tailWord_3096405
  simp only [CollatzResearch.WordTrace]
  refine ⟨112935168347260983717290669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75290112231507322478193779 112935168347260983717290669)
  ·
    refine ⟨42350688130222868893984001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112935168347260983717290669 42350688130222868893984001)
    ·
      refine ⟨31763016097667151670488001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42350688130222868893984001 31763016097667151670488001)
      ·
        refine ⟨23822262073250363752866001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31763016097667151670488001 23822262073250363752866001)
        ·
          refine ⟨17866696554937772814649501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23822262073250363752866001 17866696554937772814649501)
          ·
            refine ⟨6700011208101664805493563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17866696554937772814649501 6700011208101664805493563)
            ·
              refine ⟨10050016812152497208240345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700011208101664805493563 10050016812152497208240345)
              ·
                refine ⟨7537512609114372906180259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10050016812152497208240345 7537512609114372906180259)
                ·
                  refine ⟨11306268913671559359270389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7537512609114372906180259 11306268913671559359270389)
                  ·
                    refine ⟨1059962710656708689931599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11306268913671559359270389 1059962710656708689931599)
                    ·
                      rfl

theorem cell22_3096405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3096405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096405 prefixEnd_3096405 := by exact prefixLift 3096405
  have htrace : WordTrace (prefixWord ++ tailWord_3096405) baseStart_3096405 baseEnd_3096405 := by
    simpa [prefixWord, tailWord_3096405, baseEnd_3096405] using wordTrace_append hprefix tailTrace_3096405
  have hstable : (prefixWord ++ tailWord_3096405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096405).length < 2 ^ (prefixWord ++ tailWord_3096405).sum := by decide
  have hdescent : baseEnd_3096405 < baseStart_3096405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096448 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_3096448 : Nat := 118140960795 + 3096448 * 2 ^ 59
def prefixEnd_3096448 : Nat := 4983230072969 + 3 ^ 40 * 3096448 * 2
def baseEnd_3096448 : Nat := 1059977430435470911106467

theorem tailTrace_3096448 : CollatzResearch.WordTrace tailWord_3096448 prefixEnd_3096448 1059977430435470911106467 := by
  unfold tailWord_3096448
  simp only [CollatzResearch.WordTrace]
  refine ⟨56468368343052601030552999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75291157790736801374070665 56468368343052601030552999)
  ·
    refine ⟨84702552514578901545829499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56468368343052601030552999 84702552514578901545829499)
    ·
      refine ⟨127053828771868352318744249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84702552514578901545829499 127053828771868352318744249)
      ·
        refine ⟨95290371578901264239058187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127053828771868352318744249 95290371578901264239058187)
        ·
          refine ⟨142935557368351896358587281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95290371578901264239058187 142935557368351896358587281)
          ·
            refine ⟨107201668026263922268940461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142935557368351896358587281 107201668026263922268940461)
            ·
              refine ⟨40200625509848970850852673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107201668026263922268940461 40200625509848970850852673)
              ·
                refine ⟨30150469132386728138139505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40200625509848970850852673 30150469132386728138139505)
                ·
                  refine ⟨22612851849290046103604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30150469132386728138139505 22612851849290046103604629)
                  ·
                    refine ⟨1059977430435470911106467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22612851849290046103604629 1059977430435470911106467)
                    ·
                      rfl

theorem cell22_3096448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_3096448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096448 prefixEnd_3096448 := by exact prefixLift 3096448
  have htrace : WordTrace (prefixWord ++ tailWord_3096448) baseStart_3096448 baseEnd_3096448 := by
    simpa [prefixWord, tailWord_3096448, baseEnd_3096448] using wordTrace_append hprefix tailTrace_3096448
  have hstable : (prefixWord ++ tailWord_3096448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096448).length < 2 ^ (prefixWord ++ tailWord_3096448).sum := by decide
  have hdescent : baseEnd_3096448 < baseStart_3096448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096484 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_3096484 : Nat := 118140960795 + 3096484 * 2 ^ 59
def prefixEnd_3096484 : Nat := 4983230072969 + 3 ^ 40 * 3096484 * 2
def baseEnd_3096484 : Nat := 1059989753971178817206357

theorem tailTrace_3096484 : CollatzResearch.WordTrace tailWord_3096484 prefixEnd_3096484 1059989753971178817206357 := by
  unfold tailWord_3096484
  simp only [CollatzResearch.WordTrace]
  refine ⟨56469024856987390104708253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75292033142649853472944337 56469024856987390104708253)
  ·
    refine ⟨21175884321370271289265595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56469024856987390104708253 21175884321370271289265595)
    ·
      refine ⟨31763826482055406933898393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21175884321370271289265595 31763826482055406933898393)
      ·
        refine ⟨23822869861541555200423795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31763826482055406933898393 23822869861541555200423795)
        ·
          refine ⟨35734304792312332800635693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23822869861541555200423795 35734304792312332800635693)
          ·
            refine ⟨13400364297117124800238385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35734304792312332800635693 13400364297117124800238385)
            ·
              refine ⟨10050273222837843600178789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13400364297117124800238385 10050273222837843600178789)
              ·
                refine ⟨1884426229282095675033523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10050273222837843600178789 1884426229282095675033523)
                ·
                  refine ⟨2826639343923143512550285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884426229282095675033523 2826639343923143512550285)
                  ·
                    refine ⟨1059989753971178817206357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826639343923143512550285 1059989753971178817206357)
                    ·
                      rfl

theorem cell22_3096484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_3096484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096484 prefixEnd_3096484 := by exact prefixLift 3096484
  have htrace : WordTrace (prefixWord ++ tailWord_3096484) baseStart_3096484 baseEnd_3096484 := by
    simpa [prefixWord, tailWord_3096484, baseEnd_3096484] using wordTrace_append hprefix tailTrace_3096484
  have hstable : (prefixWord ++ tailWord_3096484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096484).length < 2 ^ (prefixWord ++ tailWord_3096484).sum := by decide
  have hdescent : baseEnd_3096484 < baseStart_3096484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096561 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_3096561 : Nat := 118140960795 + 3096561 * 2 ^ 59
def prefixEnd_3096561 : Nat := 4983230072969 + 3 ^ 40 * 3096561 * 2
def baseEnd_3096561 : Nat := 1060016112644776283031121

theorem tailTrace_3096561 : CollatzResearch.WordTrace tailWord_3096561 prefixEnd_3096561 1060016112644776283031121 := by
  unfold tailWord_3096561
  simp only [CollatzResearch.WordTrace]
  refine ⟨112940858134695822359969537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75293905423130548239979691 112940858134695822359969537)
  ·
    refine ⟨84705643601021866769977153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112940858134695822359969537 84705643601021866769977153)
    ·
      refine ⟨63529232700766400077482865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84705643601021866769977153 63529232700766400077482865)
      ·
        refine ⟨47646924525574800058112149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63529232700766400077482865 47646924525574800058112149)
        ·
          refine ⟨2233449587136318752724007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47646924525574800058112149 2233449587136318752724007)
          ·
            refine ⟨3350174380704478129086011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233449587136318752724007 3350174380704478129086011)
            ·
              refine ⟨5025261571056717193629017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350174380704478129086011 5025261571056717193629017)
              ·
                refine ⟨3768946178292537895221763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5025261571056717193629017 3768946178292537895221763)
                ·
                  refine ⟨5653419267438806842832645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768946178292537895221763 5653419267438806842832645)
                  ·
                    refine ⟨1060016112644776283031121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653419267438806842832645 1060016112644776283031121)
                    ·
                      rfl

theorem cell22_3096561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_3096561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096561 prefixEnd_3096561 := by exact prefixLift 3096561
  have htrace : WordTrace (prefixWord ++ tailWord_3096561) baseStart_3096561 baseEnd_3096561 := by
    simpa [prefixWord, tailWord_3096561, baseEnd_3096561] using wordTrace_append hprefix tailTrace_3096561
  have hstable : (prefixWord ++ tailWord_3096561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096561).length < 2 ^ (prefixWord ++ tailWord_3096561).sum := by decide
  have hdescent : baseEnd_3096561 < baseStart_3096561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096572 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3096572 : Nat := 118140960795 + 3096572 * 2 ^ 59
def prefixEnd_3096572 : Nat := 4983230072969 + 3 ^ 40 * 3096572 * 2
def baseEnd_3096572 : Nat := 1060019878169575921006087

theorem tailTrace_3096572 : CollatzResearch.WordTrace tailWord_3096572 prefixEnd_3096572 1060019878169575921006087 := by
  unfold tailWord_3096572
  simp only [CollatzResearch.WordTrace]
  refine ⟨56470629668827985619309985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75294172891770647492413313 56470629668827985619309985)
  ·
    refine ⟨42352972251620989214482489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56470629668827985619309985 42352972251620989214482489)
    ·
      refine ⟨31764729188715741910861867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42352972251620989214482489 31764729188715741910861867)
      ·
        refine ⟨47647093783073612866292801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31764729188715741910861867 47647093783073612866292801)
        ·
          refine ⟨35735320337305209649719601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47647093783073612866292801 35735320337305209649719601)
          ·
            refine ⟨26801490252978907237289701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35735320337305209649719601 26801490252978907237289701)
            ·
              refine ⟨5025279422433545106991819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26801490252978907237289701 5025279422433545106991819)
              ·
                refine ⟨7537919133650317660487729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5025279422433545106991819 7537919133650317660487729)
                ·
                  refine ⟨5653439350237738245365797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7537919133650317660487729 5653439350237738245365797)
                  ·
                    refine ⟨1060019878169575921006087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653439350237738245365797 1060019878169575921006087)
                    ·
                      rfl

theorem cell22_3096572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3096572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096572 prefixEnd_3096572 := by exact prefixLift 3096572
  have htrace : WordTrace (prefixWord ++ tailWord_3096572) baseStart_3096572 baseEnd_3096572 := by
    simpa [prefixWord, tailWord_3096572, baseEnd_3096572] using wordTrace_append hprefix tailTrace_3096572
  have hstable : (prefixWord ++ tailWord_3096572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096572).length < 2 ^ (prefixWord ++ tailWord_3096572).sum := by decide
  have hdescent : baseEnd_3096572 < baseStart_3096572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096574 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3096574 : Nat := 118140960795 + 3096574 * 2 ^ 59
def prefixEnd_3096574 : Nat := 4983230072969 + 3 ^ 40 * 3096574 * 2
def baseEnd_3096574 : Nat := 1060020562810448582456081

theorem tailTrace_3096574 : CollatzResearch.WordTrace tailWord_3096574 prefixEnd_3096574 1060020562810448582456081 := by
  unfold tailWord_3096574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14117666535456090697524097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75294221522432483720128517 14117666535456090697524097)
  ·
    refine ⟨10588249901592068023143073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14117666535456090697524097 10588249901592068023143073)
    ·
      refine ⟨7941187426194051017357305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10588249901592068023143073 7941187426194051017357305)
      ·
        refine ⟨5955890569645538263017979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7941187426194051017357305 5955890569645538263017979)
        ·
          refine ⟨8933835854468307394526969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5955890569645538263017979 8933835854468307394526969)
          ·
            refine ⟨6700376890851230545895227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8933835854468307394526969 6700376890851230545895227)
            ·
              refine ⟨10050565336276845818842841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6700376890851230545895227 10050565336276845818842841)
              ·
                refine ⟨7537924002207634364132131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10050565336276845818842841 7537924002207634364132131)
                ·
                  refine ⟨11306886003311451546198197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7537924002207634364132131 11306886003311451546198197)
                  ·
                    refine ⟨1060020562810448582456081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11306886003311451546198197 1060020562810448582456081)
                    ·
                      rfl

theorem cell22_3096574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3096574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096574 prefixEnd_3096574 := by exact prefixLift 3096574
  have htrace : WordTrace (prefixWord ++ tailWord_3096574) baseStart_3096574 baseEnd_3096574 := by
    simpa [prefixWord, tailWord_3096574, baseEnd_3096574] using wordTrace_append hprefix tailTrace_3096574
  have hstable : (prefixWord ++ tailWord_3096574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096574).length < 2 ^ (prefixWord ++ tailWord_3096574).sum := by decide
  have hdescent : baseEnd_3096574 < baseStart_3096574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096600 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3096600 : Nat := 118140960795 + 3096600 * 2 ^ 59
def prefixEnd_3096600 : Nat := 4983230072969 + 3 ^ 40 * 3096600 * 2
def baseEnd_3096600 : Nat := 1060029463141793181306001

theorem tailTrace_3096600 : CollatzResearch.WordTrace tailWord_3096600 prefixEnd_3096600 1060029463141793181306001 := by
  unfold tailWord_3096600
  simp only [CollatzResearch.WordTrace]
  refine ⟨56471140290777266010319627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75294853721036354680426169 56471140290777266010319627)
  ·
    refine ⟨84706710436165899015479441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56471140290777266010319627 84706710436165899015479441)
    ·
      refine ⟨63530032827124424261609581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84706710436165899015479441 63530032827124424261609581)
      ·
        refine ⟨23823762310171659098103593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63530032827124424261609581 23823762310171659098103593)
        ·
          refine ⟨17867821732628744323577695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23823762310171659098103593 17867821732628744323577695)
          ·
            refine ⟨26801732598943116485366543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17867821732628744323577695 26801732598943116485366543)
            ·
              refine ⟨40202598898414674728049815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26801732598943116485366543 40202598898414674728049815)
              ·
                refine ⟨60303898347622012092074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40202598898414674728049815 60303898347622012092074723)
                ·
                  refine ⟨90455847521433018138112085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60303898347622012092074723 90455847521433018138112085)
                  ·
                    refine ⟨1060029463141793181306001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90455847521433018138112085 1060029463141793181306001)
                    ·
                      rfl

theorem cell22_3096600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3096600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096600 prefixEnd_3096600 := by exact prefixLift 3096600
  have htrace : WordTrace (prefixWord ++ tailWord_3096600) baseStart_3096600 baseEnd_3096600 := by
    simpa [prefixWord, tailWord_3096600, baseEnd_3096600] using wordTrace_append hprefix tailTrace_3096600
  have hstable : (prefixWord ++ tailWord_3096600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096600).length < 2 ^ (prefixWord ++ tailWord_3096600).sum := by decide
  have hdescent : baseEnd_3096600 < baseStart_3096600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096636 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_3096636 : Nat := 118140960795 + 3096636 * 2 ^ 59
def prefixEnd_3096636 : Nat := 4983230072969 + 3 ^ 40 * 3096636 * 2
def baseEnd_3096636 : Nat := 1060041786677501087405891

theorem tailTrace_3096636 : CollatzResearch.WordTrace tailWord_3096636 prefixEnd_3096636 1060041786677501087405891 := by
  unfold tailWord_3096636
  simp only [CollatzResearch.WordTrace]
  refine ⟨56471796804712055084474881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75295729072949406779299841 56471796804712055084474881)
  ·
    refine ⟨42353847603534041313356161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56471796804712055084474881 42353847603534041313356161)
    ·
      refine ⟨31765385702650530985017121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42353847603534041313356161 31765385702650530985017121)
      ·
        refine ⟨23824039276987898238762841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31765385702650530985017121 23824039276987898238762841)
        ·
          refine ⟨17868029457740923679072131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23824039276987898238762841 17868029457740923679072131)
          ·
            refine ⟨26802044186611385518608197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17868029457740923679072131 26802044186611385518608197)
            ·
              refine ⟨5025383284989634784739037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26802044186611385518608197 5025383284989634784739037)
              ·
                refine ⟨1884518731871113044277139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5025383284989634784739037 1884518731871113044277139)
                ·
                  refine ⟨2826778097806669566415709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884518731871113044277139 2826778097806669566415709)
                  ·
                    refine ⟨1060041786677501087405891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826778097806669566415709 1060041786677501087405891)
                    ·
                      rfl

theorem cell22_3096636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_3096636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096636 prefixEnd_3096636 := by exact prefixLift 3096636
  have htrace : WordTrace (prefixWord ++ tailWord_3096636) baseStart_3096636 baseEnd_3096636 := by
    simpa [prefixWord, tailWord_3096636, baseEnd_3096636] using wordTrace_append hprefix tailTrace_3096636
  have hstable : (prefixWord ++ tailWord_3096636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096636).length < 2 ^ (prefixWord ++ tailWord_3096636).sum := by decide
  have hdescent : baseEnd_3096636 < baseStart_3096636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096677 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 6]
def baseStart_3096677 : Nat := 118140960795 + 3096677 * 2 ^ 59
def prefixEnd_3096677 : Nat := 4983230072969 + 3 ^ 40 * 3096677 * 2
def baseEnd_3096677 : Nat := 353351940605130215710255

theorem tailTrace_3096677 : CollatzResearch.WordTrace tailWord_3096677 prefixEnd_3096677 353351940605130215710255 := by
  unfold tailWord_3096677
  simp only [CollatzResearch.WordTrace]
  refine ⟨112945089002275574171192285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75296726001517049447461523 112945089002275574171192285)
  ·
    refine ⟨42354408375853340314197107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112945089002275574171192285 42354408375853340314197107)
    ·
      refine ⟨63531612563780010471295661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42354408375853340314197107 63531612563780010471295661)
      ·
        refine ⟨23824354711417503926735873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63531612563780010471295661 23824354711417503926735873)
        ·
          refine ⟨17868266033563127945051905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23824354711417503926735873 17868266033563127945051905)
          ·
            refine ⟨13401199525172345958788929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17868266033563127945051905 13401199525172345958788929)
            ·
              refine ⟨10050899643879259469091697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401199525172345958788929 10050899643879259469091697)
              ·
                refine ⟨7538174732909444601818773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10050899643879259469091697 7538174732909444601818773)
                ·
                  refine ⟨353351940605130215710255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7538174732909444601818773 353351940605130215710255)
                  ·
                    rfl

theorem cell22_3096677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_3096677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096677 prefixEnd_3096677 := by exact prefixLift 3096677
  have htrace : WordTrace (prefixWord ++ tailWord_3096677) baseStart_3096677 baseEnd_3096677 := by
    simpa [prefixWord, tailWord_3096677, baseEnd_3096677] using wordTrace_append hprefix tailTrace_3096677
  have hstable : (prefixWord ++ tailWord_3096677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096677).length < 2 ^ (prefixWord ++ tailWord_3096677).sum := by decide
  have hdescent : baseEnd_3096677 < baseStart_3096677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096679 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3096679 : Nat := 118140960795 + 3096679 * 2 ^ 59
def prefixEnd_3096679 : Nat := 4983230072969 + 3 ^ 40 * 3096679 * 2
def baseEnd_3096679 : Nat := 1060056506456263308580759

theorem tailTrace_3096679 : CollatzResearch.WordTrace tailWord_3096679 prefixEnd_3096679 1060056506456263308580759 := by
  unfold tailWord_3096679
  simp only [CollatzResearch.WordTrace]
  refine ⟨112945161948268328512765091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75296774632178885675176727 112945161948268328512765091)
  ·
    refine ⟨169417742922402492769147637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112945161948268328512765091 169417742922402492769147637)
    ·
      refine ⟨15882913398975233697107591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169417742922402492769147637 15882913398975233697107591)
      ·
        refine ⟨23824370098462850545661387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15882913398975233697107591 23824370098462850545661387)
        ·
          refine ⟨35736555147694275818492081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23824370098462850545661387 35736555147694275818492081)
          ·
            refine ⟨26802416360770706863869061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35736555147694275818492081 26802416360770706863869061)
            ·
              refine ⟨5025453067644507536975449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26802416360770706863869061 5025453067644507536975449)
              ·
                refine ⟨3769089800733380652731587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5025453067644507536975449 3769089800733380652731587)
                ·
                  refine ⟨5653634701100070979097381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769089800733380652731587 5653634701100070979097381)
                  ·
                    refine ⟨1060056506456263308580759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653634701100070979097381 1060056506456263308580759)
                    ·
                      rfl

theorem cell22_3096679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3096679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096679 prefixEnd_3096679 := by exact prefixLift 3096679
  have htrace : WordTrace (prefixWord ++ tailWord_3096679) baseStart_3096679 baseEnd_3096679 := by
    simpa [prefixWord, tailWord_3096679, baseEnd_3096679] using wordTrace_append hprefix tailTrace_3096679
  have hstable : (prefixWord ++ tailWord_3096679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096679).length < 2 ^ (prefixWord ++ tailWord_3096679).sum := by decide
  have hdescent : baseEnd_3096679 < baseStart_3096679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096707 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_3096707 : Nat := 118140960795 + 3096707 * 2 ^ 59
def prefixEnd_3096707 : Nat := 4983230072969 + 3 ^ 40 * 3096707 * 2
def baseEnd_3096707 : Nat := 1060066091428480568880673

theorem tailTrace_3096707 : CollatzResearch.WordTrace tailWord_3096707 prefixEnd_3096707 1060066091428480568880673 := by
  unfold tailWord_3096707
  simp only [CollatzResearch.WordTrace]
  refine ⟨112946183192166889294784375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75297455461444592863189583 112946183192166889294784375)
  ·
    refine ⟨169419274788250333942176563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112946183192166889294784375 169419274788250333942176563)
    ·
      refine ⟨254128912182375500913264845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169419274788250333942176563 254128912182375500913264845)
      ·
        refine ⟨95298342068390812842474317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254128912182375500913264845 95298342068390812842474317)
        ·
          refine ⟨35736878275646554815927869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95298342068390812842474317 35736878275646554815927869)
          ·
            refine ⟨13401329353367458055972951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35736878275646554815927869 13401329353367458055972951)
            ·
              refine ⟨20101994030051187083959427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401329353367458055972951 20101994030051187083959427)
              ·
                refine ⟨30152991045076780625939141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20101994030051187083959427 30152991045076780625939141)
                ·
                  refine ⟨5653685820951896367363589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30152991045076780625939141 5653685820951896367363589)
                  ·
                    refine ⟨1060066091428480568880673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5653685820951896367363589 1060066091428480568880673)
                    ·
                      rfl

theorem cell22_3096707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_3096707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096707 prefixEnd_3096707 := by exact prefixLift 3096707
  have htrace : WordTrace (prefixWord ++ tailWord_3096707) baseStart_3096707 baseEnd_3096707 := by
    simpa [prefixWord, tailWord_3096707, baseEnd_3096707] using wordTrace_append hprefix tailTrace_3096707
  have hstable : (prefixWord ++ tailWord_3096707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096707).length < 2 ^ (prefixWord ++ tailWord_3096707).sum := by decide
  have hdescent : baseEnd_3096707 < baseStart_3096707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096709 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_3096709 : Nat := 118140960795 + 3096709 * 2 ^ 59
def prefixEnd_3096709 : Nat := 4983230072969 + 3 ^ 40 * 3096709 * 2
def baseEnd_3096709 : Nat := 1060066776069353230330667

theorem tailTrace_3096709 : CollatzResearch.WordTrace tailWord_3096709 prefixEnd_3096709 1060066776069353230330667 := by
  unfold tailWord_3096709
  simp only [CollatzResearch.WordTrace]
  refine ⟨112946256138159643636357181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75297504092106429090904787 112946256138159643636357181)
  ·
    refine ⟨42354846051809866363633943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112946256138159643636357181 42354846051809866363633943)
    ·
      refine ⟨63532269077714799545450915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42354846051809866363633943 63532269077714799545450915)
      ·
        refine ⟨95298403616572199318176373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63532269077714799545450915 95298403616572199318176373)
        ·
          refine ⟨8934225339053643686079035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95298403616572199318176373 8934225339053643686079035)
          ·
            refine ⟨13401338008580465529118553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934225339053643686079035 13401338008580465529118553)
            ·
              refine ⟨10051003506435349146838915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401338008580465529118553 10051003506435349146838915)
              ·
                refine ⟨15076505259653023720258373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10051003506435349146838915 15076505259653023720258373)
                ·
                  refine ⟨2826844736184941947548445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15076505259653023720258373 2826844736184941947548445)
                  ·
                    refine ⟨1060066776069353230330667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826844736184941947548445 1060066776069353230330667)
                    ·
                      rfl

theorem cell22_3096709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_3096709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096709 prefixEnd_3096709 := by exact prefixLift 3096709
  have htrace : WordTrace (prefixWord ++ tailWord_3096709) baseStart_3096709 baseEnd_3096709 := by
    simpa [prefixWord, tailWord_3096709, baseEnd_3096709] using wordTrace_append hprefix tailTrace_3096709
  have hstable : (prefixWord ++ tailWord_3096709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096709).length < 2 ^ (prefixWord ++ tailWord_3096709).sum := by decide
  have hdescent : baseEnd_3096709 < baseStart_3096709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096756 : List Nat := [2, 5, 3, 1, 11]
def baseStart_3096756 : Nat := 118140960795 + 3096756 * 2 ^ 59
def prefixEnd_3096756 : Nat := 4983230072969 + 3 ^ 40 * 3096756 * 2
def baseEnd_3096756 : Nat := 4362480926460332404961

theorem tailTrace_3096756 : CollatzResearch.WordTrace tailWord_3096756 prefixEnd_3096756 4362480926460332404961 := by
  unfold tailWord_3096756
  simp only [CollatzResearch.WordTrace]
  refine ⟨56473985184494685331659061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75298646912659580442212081 56473985184494685331659061)
  ·
    refine ⟨5294436111046376749843037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56473985184494685331659061 5294436111046376749843037)
    ·
      refine ⟨1985413541642391281191139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5294436111046376749843037 1985413541642391281191139)
      ·
        refine ⟨2978120312463586921786709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985413541642391281191139 2978120312463586921786709)
        ·
          refine ⟨4362480926460332404961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2978120312463586921786709 4362480926460332404961)
          ·
            rfl

theorem cell22_3096756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 11].length) (baseStart_3096756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096756 prefixEnd_3096756 := by exact prefixLift 3096756
  have htrace : WordTrace (prefixWord ++ tailWord_3096756) baseStart_3096756 baseEnd_3096756 := by
    simpa [prefixWord, tailWord_3096756, baseEnd_3096756] using wordTrace_append hprefix tailTrace_3096756
  have hstable : (prefixWord ++ tailWord_3096756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096756).length < 2 ^ (prefixWord ++ tailWord_3096756).sum := by decide
  have hdescent : baseEnd_3096756 < baseStart_3096756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096812 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_3096812 : Nat := 118140960795 + 3096812 * 2 ^ 59
def prefixEnd_3096812 : Nat := 4983230072969 + 3 ^ 40 * 3096812 * 2
def baseEnd_3096812 : Nat := 353367345024765098335117

theorem tailTrace_3096812 : CollatzResearch.WordTrace tailWord_3096812 prefixEnd_3096812 353367345024765098335117 := by
  unfold tailWord_3096812
  simp only [CollatzResearch.WordTrace]
  refine ⟨56475006428393246113678345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75300008571190994818237793 56475006428393246113678345)
  ·
    refine ⟨42356254821294934585258759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56475006428393246113678345 42356254821294934585258759)
    ·
      refine ⟨63534382231942401877888139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42356254821294934585258759 63534382231942401877888139)
      ·
        refine ⟨95301573347913602816832209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63534382231942401877888139 95301573347913602816832209)
        ·
          refine ⟨71476180010935202112624157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95301573347913602816832209 71476180010935202112624157)
          ·
            refine ⟨26803567504100700792234059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71476180010935202112624157 26803567504100700792234059)
            ·
              refine ⟨40205351256151051188351089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26803567504100700792234059 40205351256151051188351089)
              ·
                refine ⟨30154013442113288391263317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40205351256151051188351089 30154013442113288391263317)
                ·
                  refine ⟨353367345024765098335117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30154013442113288391263317 353367345024765098335117)
                  ·
                    rfl

theorem cell22_3096812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_3096812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096812 prefixEnd_3096812 := by exact prefixLift 3096812
  have htrace : WordTrace (prefixWord ++ tailWord_3096812) baseStart_3096812 baseEnd_3096812 := by
    simpa [prefixWord, tailWord_3096812, baseEnd_3096812] using wordTrace_append hprefix tailTrace_3096812
  have hstable : (prefixWord ++ tailWord_3096812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096812).length < 2 ^ (prefixWord ++ tailWord_3096812).sum := by decide
  have hdescent : baseEnd_3096812 < baseStart_3096812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096863 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 4]
def baseStart_3096863 : Nat := 118140960795 + 3096863 * 2 ^ 59
def prefixEnd_3096863 : Nat := 4983230072969 + 3 ^ 40 * 3096863 * 2
def baseEnd_3096863 : Nat := 353373164472182720660065

theorem tailTrace_3096863 : CollatzResearch.WordTrace tailWord_3096863 prefixEnd_3096863 353373164472182720660065 := by
  unfold tailWord_3096863
  simp only [CollatzResearch.WordTrace]
  refine ⟨112951872979601727937463243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75301248653067818624975495 112951872979601727937463243)
  ·
    refine ⟨169427809469402591906194865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112951872979601727937463243 169427809469402591906194865)
    ·
      refine ⟨127070857102051943929646149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169427809469402591906194865 127070857102051943929646149)
      ·
        refine ⟨23825785706634739486808653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127070857102051943929646149 23825785706634739486808653)
        ·
          refine ⟨8934669639988027307553245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23825785706634739486808653 8934669639988027307553245)
          ·
            refine ⟨3350501114995510240332467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8934669639988027307553245 3350501114995510240332467)
            ·
              refine ⟨5025751672493265360498701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350501114995510240332467 5025751672493265360498701)
              ·
                refine ⟨1884656877184974510187013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5025751672493265360498701 1884656877184974510187013)
                ·
                  refine ⟨353373164472182720660065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1884656877184974510187013 353373164472182720660065)
                  ·
                    rfl

theorem cell22_3096863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 4].length) (baseStart_3096863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096863 prefixEnd_3096863 := by exact prefixLift 3096863
  have htrace : WordTrace (prefixWord ++ tailWord_3096863) baseStart_3096863 baseEnd_3096863 := by
    simpa [prefixWord, tailWord_3096863, baseEnd_3096863] using wordTrace_append hprefix tailTrace_3096863
  have hstable : (prefixWord ++ tailWord_3096863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096863).length < 2 ^ (prefixWord ++ tailWord_3096863).sum := by decide
  have hdescent : baseEnd_3096863 < baseStart_3096863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096936 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_3096936 : Nat := 118140960795 + 3096936 * 2 ^ 59
def prefixEnd_3096936 : Nat := 4983230072969 + 3 ^ 40 * 3096936 * 2
def baseEnd_3096936 : Nat := 353381494269466768301657

theorem tailTrace_3096936 : CollatzResearch.WordTrace tailWord_3096936 prefixEnd_3096936 353381494269466768301657 := by
  unfold tailWord_3096936
  simp only [CollatzResearch.WordTrace]
  refine ⟨56477267754168630702435331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75303023672224840936580441 56477267754168630702435331)
  ·
    refine ⟨84715901631252946053652997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56477267754168630702435331 84715901631252946053652997)
    ·
      refine ⟨15884231555859927385059937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84715901631252946053652997 15884231555859927385059937)
      ·
        refine ⟨11913173666894945538794953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15884231555859927385059937 11913173666894945538794953)
        ·
          refine ⟨8934880250171209154096215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11913173666894945538794953 8934880250171209154096215)
          ·
            refine ⟨13402320375256813731144323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934880250171209154096215 13402320375256813731144323)
            ·
              refine ⟨20103480562885220596716485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13402320375256813731144323 20103480562885220596716485)
              ·
                refine ⟨3769402605540978861884341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20103480562885220596716485 3769402605540978861884341)
                ·
                  refine ⟨353381494269466768301657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3769402605540978861884341 353381494269466768301657)
                  ·
                    rfl

theorem cell22_3096936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_3096936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096936 prefixEnd_3096936 := by exact prefixLift 3096936
  have htrace : WordTrace (prefixWord ++ tailWord_3096936) baseStart_3096936 baseEnd_3096936 := by
    simpa [prefixWord, tailWord_3096936, baseEnd_3096936] using wordTrace_append hprefix tailTrace_3096936
  have hstable : (prefixWord ++ tailWord_3096936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096936).length < 2 ^ (prefixWord ++ tailWord_3096936).sum := by decide
  have hdescent : baseEnd_3096936 < baseStart_3096936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096940 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_3096940 : Nat := 118140960795 + 3096940 * 2 ^ 59
def prefixEnd_3096940 : Nat := 4983230072969 + 3 ^ 40 * 3096940 * 2
def baseEnd_3096940 : Nat := 1060145852090145627804959

theorem tailTrace_3096940 : CollatzResearch.WordTrace tailWord_3096940 prefixEnd_3096940 1060145852090145627804959 := by
  unfold tailWord_3096940
  simp only [CollatzResearch.WordTrace]
  refine ⟨56477340700161385044008137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75303120933548513392010849 56477340700161385044008137)
  ·
    refine ⟨42358005525121038783006103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56477340700161385044008137 42358005525121038783006103)
    ·
      refine ⟨63537008287681558174509155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42358005525121038783006103 63537008287681558174509155)
      ·
        refine ⟨95305512431522337261763733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63537008287681558174509155 95305512431522337261763733)
        ·
          refine ⟨4467445895227609559145175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95305512431522337261763733 4467445895227609559145175)
          ·
            refine ⟨6701168842841414338717763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467445895227609559145175 6701168842841414338717763)
            ·
              refine ⟨10051753264262121508076645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701168842841414338717763 10051753264262121508076645)
              ·
                refine ⟨1884703737049147782764371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10051753264262121508076645 1884703737049147782764371)
                ·
                  refine ⟨2827055605573721674146557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884703737049147782764371 2827055605573721674146557)
                  ·
                    refine ⟨1060145852090145627804959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827055605573721674146557 1060145852090145627804959)
                    ·
                      rfl

theorem cell22_3096940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_3096940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096940 prefixEnd_3096940 := by exact prefixLift 3096940
  have htrace : WordTrace (prefixWord ++ tailWord_3096940) baseStart_3096940 baseEnd_3096940 := by
    simpa [prefixWord, tailWord_3096940, baseEnd_3096940] using wordTrace_append hprefix tailTrace_3096940
  have hstable : (prefixWord ++ tailWord_3096940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096940).length < 2 ^ (prefixWord ++ tailWord_3096940).sum := by decide
  have hdescent : baseEnd_3096940 < baseStart_3096940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3096983 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 1, 4]
def baseStart_3096983 : Nat := 118140960795 + 3096983 * 2 ^ 59
def prefixEnd_3096983 : Nat := 4983230072969 + 3 ^ 40 * 3096983 * 2
def baseEnd_3096983 : Nat := 1060160571868907848979827

theorem tailTrace_3096983 : CollatzResearch.WordTrace tailWord_3096983 prefixEnd_3096983 1060160571868907848979827 := by
  unfold tailWord_3096983
  simp only [CollatzResearch.WordTrace]
  refine ⟨112956249739166988431831603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75304166492777992287887735 112956249739166988431831603)
  ·
    refine ⟨169434374608750482647747405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112956249739166988431831603 169434374608750482647747405)
    ·
      refine ⟨63537890478281430992905277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169434374608750482647747405 63537890478281430992905277)
      ·
        refine ⟨23826708929355536622339479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63537890478281430992905277 23826708929355536622339479)
        ·
          refine ⟨35740063394033304933509219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23826708929355536622339479 35740063394033304933509219)
          ·
            refine ⟨53610095091049957400263829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35740063394033304933509219 53610095091049957400263829)
            ·
              refine ⟨2512973207392966753137367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53610095091049957400263829 2512973207392966753137367)
              ·
                refine ⟨3769459811089450129706051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512973207392966753137367 3769459811089450129706051)
                ·
                  refine ⟨5654189716634175194559077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769459811089450129706051 5654189716634175194559077)
                  ·
                    refine ⟨1060160571868907848979827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5654189716634175194559077 1060160571868907848979827)
                    ·
                      rfl

theorem cell22_3096983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_3096983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3096983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3096983 prefixEnd_3096983 := by exact prefixLift 3096983
  have htrace : WordTrace (prefixWord ++ tailWord_3096983) baseStart_3096983 baseEnd_3096983 := by
    simpa [prefixWord, tailWord_3096983, baseEnd_3096983] using wordTrace_append hprefix tailTrace_3096983
  have hstable : (prefixWord ++ tailWord_3096983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3096983).length < 2 ^ (prefixWord ++ tailWord_3096983).sum := by decide
  have hdescent : baseEnd_3096983 < baseStart_3096983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3096983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097024 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_3097024 : Nat := 118140960795 + 3097024 * 2 ^ 59
def prefixEnd_3097024 : Nat := 4983230072969 + 3 ^ 40 * 3097024 * 2
def baseEnd_3097024 : Nat := 1060174607006797408704701

theorem tailTrace_3097024 : CollatzResearch.WordTrace tailWord_3097024 prefixEnd_3097024 1060174607006797408704701 := by
  unfold tailWord_3097024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56478872566009226217037063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75305163421345634956049417 56478872566009226217037063)
  ·
    refine ⟨84718308849013839325555595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56478872566009226217037063 84718308849013839325555595)
    ·
      refine ⟨127077463273520758988333393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84718308849013839325555595 127077463273520758988333393)
      ·
        refine ⟨95308097455140569241250045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127077463273520758988333393 95308097455140569241250045)
        ·
          refine ⟨35740536545677713465468767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95308097455140569241250045 35740536545677713465468767)
          ·
            refine ⟨53610804818516570198203151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35740536545677713465468767 53610804818516570198203151)
            ·
              refine ⟨80416207227774855297304727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53610804818516570198203151 80416207227774855297304727)
              ·
                refine ⟨120624310841662282945957091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80416207227774855297304727 120624310841662282945957091)
                ·
                  refine ⟨180936466262493424418935637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120624310841662282945957091 180936466262493424418935637)
                  ·
                    refine ⟨1060174607006797408704701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180936466262493424418935637 1060174607006797408704701)
                    ·
                      rfl

theorem cell22_3097024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_3097024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097024 prefixEnd_3097024 := by exact prefixLift 3097024
  have htrace : WordTrace (prefixWord ++ tailWord_3097024) baseStart_3097024 baseEnd_3097024 := by
    simpa [prefixWord, tailWord_3097024, baseEnd_3097024] using wordTrace_append hprefix tailTrace_3097024
  have hstable : (prefixWord ++ tailWord_3097024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097024).length < 2 ^ (prefixWord ++ tailWord_3097024).sum := by decide
  have hdescent : baseEnd_3097024 < baseStart_3097024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097039 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3097039 : Nat := 118140960795 + 3097039 * 2 ^ 59
def prefixEnd_3097039 : Nat := 4983230072969 + 3 ^ 40 * 3097039 * 2
def baseEnd_3097039 : Nat := 1060179741813342369579655

theorem tailTrace_3097039 : CollatzResearch.WordTrace tailWord_3097039 prefixEnd_3097039 1060179741813342369579655 := by
  unfold tailWord_3097039
  simp only [CollatzResearch.WordTrace]
  refine ⟨112958292226964109995870171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75305528151309406663913447 112958292226964109995870171)
  ·
    refine ⟨169437438340446164993805257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112958292226964109995870171 169437438340446164993805257)
    ·
      refine ⟨127078078755334623745353943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169437438340446164993805257 127078078755334623745353943)
      ·
        refine ⟨190617118133001935618030915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127078078755334623745353943 190617118133001935618030915)
        ·
          refine ⟨285925677199502903427046373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190617118133001935618030915 285925677199502903427046373)
          ·
            refine ⟨53611064474906794392571195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285925677199502903427046373 53611064474906794392571195)
            ·
              refine ⟨80416596712360191588856793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53611064474906794392571195 80416596712360191588856793)
              ·
                refine ⟨60312447534270143691642595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80416596712360191588856793 60312447534270143691642595)
                ·
                  refine ⟨90468671301405215537463893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60312447534270143691642595 90468671301405215537463893)
                  ·
                    refine ⟨1060179741813342369579655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90468671301405215537463893 1060179741813342369579655)
                    ·
                      rfl

theorem cell22_3097039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3097039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097039 prefixEnd_3097039 := by exact prefixLift 3097039
  have htrace : WordTrace (prefixWord ++ tailWord_3097039) baseStart_3097039 baseEnd_3097039 := by
    simpa [prefixWord, tailWord_3097039, baseEnd_3097039] using wordTrace_append hprefix tailTrace_3097039
  have hstable : (prefixWord ++ tailWord_3097039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097039).length < 2 ^ (prefixWord ++ tailWord_3097039).sum := by decide
  have hdescent : baseEnd_3097039 < baseStart_3097039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097041 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_3097041 : Nat := 118140960795 + 3097041 * 2 ^ 59
def prefixEnd_3097041 : Nat := 4983230072969 + 3 ^ 40 * 3097041 * 2
def baseEnd_3097041 : Nat := 1060180426454215031029649

theorem tailTrace_3097041 : CollatzResearch.WordTrace tailWord_3097041 prefixEnd_3097041 1060180426454215031029649 := by
  unfold tailWord_3097041
  simp only [CollatzResearch.WordTrace]
  refine ⟨112958365172956864337442977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75305576781971242891628651 112958365172956864337442977)
  ·
    refine ⟨84718773879717648253082233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112958365172956864337442977 84718773879717648253082233)
    ·
      refine ⟨63539080409788236189811675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84718773879717648253082233 63539080409788236189811675)
      ·
        refine ⟨95308620614682354284717513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63539080409788236189811675 95308620614682354284717513)
        ·
          refine ⟨71481465461011765713538135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95308620614682354284717513 71481465461011765713538135)
          ·
            refine ⟨107222198191517648570307203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71481465461011765713538135 107222198191517648570307203)
            ·
              refine ⟨160833297287276472855460805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107222198191517648570307203 160833297287276472855460805)
              ·
                refine ⟨30156243241364338660398901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160833297287276472855460805 30156243241364338660398901)
                ·
                  refine ⟨2827147803877906749412397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30156243241364338660398901 2827147803877906749412397)
                  ·
                    refine ⟨1060180426454215031029649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827147803877906749412397 1060180426454215031029649)
                    ·
                      rfl

theorem cell22_3097041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_3097041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097041 prefixEnd_3097041 := by exact prefixLift 3097041
  have htrace : WordTrace (prefixWord ++ tailWord_3097041) baseStart_3097041 baseEnd_3097041 := by
    simpa [prefixWord, tailWord_3097041, baseEnd_3097041] using wordTrace_append hprefix tailTrace_3097041
  have hstable : (prefixWord ++ tailWord_3097041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097041).length < 2 ^ (prefixWord ++ tailWord_3097041).sum := by decide
  have hdescent : baseEnd_3097041 < baseStart_3097041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097148 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3097148 : Nat := 118140960795 + 3097148 * 2 ^ 59
def prefixEnd_3097148 : Nat := 4983230072969 + 3 ^ 40 * 3097148 * 2
def baseEnd_3097148 : Nat := 1060217054740902418604321

theorem tailTrace_3097148 : CollatzResearch.WordTrace tailWord_3097148 prefixEnd_3097148 1060217054740902418604321 := by
  unfold tailWord_3097148
  simp only [CollatzResearch.WordTrace]
  refine ⟨56481133891784610805794049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75308178522379481074392065 56481133891784610805794049)
  ·
    refine ⟨42360850418838458104345537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56481133891784610805794049 42360850418838458104345537)
    ·
      refine ⟨31770637814128843578259153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42360850418838458104345537 31770637814128843578259153)
      ·
        refine ⟨23827978360596632683694365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31770637814128843578259153 23827978360596632683694365)
        ·
          refine ⟨8935491885223737256385387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23827978360596632683694365 8935491885223737256385387)
          ·
            refine ⟨13403237827835605884578081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8935491885223737256385387 13403237827835605884578081)
            ·
              refine ⟨10052428370876704413433561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13403237827835605884578081 10052428370876704413433561)
              ·
                refine ⟨7539321278157528310075171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10052428370876704413433561 7539321278157528310075171)
                ·
                  refine ⟨11308981917236292465112757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7539321278157528310075171 11308981917236292465112757)
                  ·
                    refine ⟨1060217054740902418604321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11308981917236292465112757 1060217054740902418604321)
                    ·
                      rfl

theorem cell22_3097148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3097148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097148 prefixEnd_3097148 := by exact prefixLift 3097148
  have htrace : WordTrace (prefixWord ++ tailWord_3097148) baseStart_3097148 baseEnd_3097148 := by
    simpa [prefixWord, tailWord_3097148, baseEnd_3097148] using wordTrace_append hprefix tailTrace_3097148
  have hstable : (prefixWord ++ tailWord_3097148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097148).length < 2 ^ (prefixWord ++ tailWord_3097148).sum := by decide
  have hdescent : baseEnd_3097148 < baseStart_3097148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097156 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3097156 : Nat := 118140960795 + 3097156 * 2 ^ 59
def prefixEnd_3097156 : Nat := 4983230072969 + 3 ^ 40 * 3097156 * 2
def baseEnd_3097156 : Nat := 353406597768131021468099

theorem tailTrace_3097156 : CollatzResearch.WordTrace tailWord_3097156 prefixEnd_3097156 353406597768131021468099 := by
  unfold tailWord_3097156
  simp only [CollatzResearch.WordTrace]
  refine ⟨56481279783770119488939661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75308373045026825985252881 56481279783770119488939661)
  ·
    refine ⟨21180479918913794808352373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56481279783770119488939661 21180479918913794808352373)
    ·
      refine ⟨1985669992398168263283035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21180479918913794808352373 1985669992398168263283035)
      ·
        refine ⟨2978504988597252394924553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985669992398168263283035 2978504988597252394924553)
        ·
          refine ⟨2233878741447939296193415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2978504988597252394924553 2233878741447939296193415)
          ·
            refine ⟨3350818112171908944290123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233878741447939296193415 3350818112171908944290123)
            ·
              refine ⟨5026227168257863416435185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350818112171908944290123 5026227168257863416435185)
              ·
                refine ⟨3769670376193397562326389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5026227168257863416435185 3769670376193397562326389)
                ·
                  refine ⟨353406597768131021468099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3769670376193397562326389 353406597768131021468099)
                  ·
                    rfl

theorem cell22_3097156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3097156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097156 prefixEnd_3097156 := by exact prefixLift 3097156
  have htrace : WordTrace (prefixWord ++ tailWord_3097156) baseStart_3097156 baseEnd_3097156 := by
    simpa [prefixWord, tailWord_3097156, baseEnd_3097156] using wordTrace_append hprefix tailTrace_3097156
  have hstable : (prefixWord ++ tailWord_3097156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097156).length < 2 ^ (prefixWord ++ tailWord_3097156).sum := by decide
  have hdescent : baseEnd_3097156 < baseStart_3097156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097218 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3097218 : Nat := 118140960795 + 3097218 * 2 ^ 59
def prefixEnd_3097218 : Nat := 4983230072969 + 3 ^ 40 * 3097218 * 2
def baseEnd_3097218 : Nat := 353413672390481856451369

theorem tailTrace_3097218 : CollatzResearch.WordTrace tailWord_3097218 prefixEnd_3097218 353413672390481856451369 := by
  unfold tailWord_3097218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28241205223328905891659077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75309880595543749044424205 28241205223328905891659077)
  ·
    refine ⟨5295225979374169854686077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28241205223328905891659077 5295225979374169854686077)
    ·
      refine ⟨1985709742265313695507279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5295225979374169854686077 1985709742265313695507279)
      ·
        refine ⟨2978564613397970543260919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985709742265313695507279 2978564613397970543260919)
        ·
          refine ⟨4467846920096955814891379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978564613397970543260919 4467846920096955814891379)
          ·
            refine ⟨6701770380145433722337069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467846920096955814891379 6701770380145433722337069)
            ·
              refine ⟨2513163892554537645876401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6701770380145433722337069 2513163892554537645876401)
              ·
                refine ⟨1884872919415903234407301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513163892554537645876401 1884872919415903234407301)
                ·
                  refine ⟨353413672390481856451369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1884872919415903234407301 353413672390481856451369)
                  ·
                    rfl

theorem cell22_3097218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3097218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097218 prefixEnd_3097218 := by exact prefixLift 3097218
  have htrace : WordTrace (prefixWord ++ tailWord_3097218) baseStart_3097218 baseEnd_3097218 := by
    simpa [prefixWord, tailWord_3097218, baseEnd_3097218] using wordTrace_append hprefix tailTrace_3097218
  have hstable : (prefixWord ++ tailWord_3097218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097218).length < 2 ^ (prefixWord ++ tailWord_3097218).sum := by decide
  have hdescent : baseEnd_3097218 < baseStart_3097218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097223 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 5]
def baseStart_3097223 : Nat := 118140960795 + 3097223 * 2 ^ 59
def prefixEnd_3097223 : Nat := 4983230072969 + 3 ^ 40 * 3097223 * 2
def baseEnd_3097223 : Nat := 353414242924542407659697

theorem tailTrace_3097223 : CollatzResearch.WordTrace tailWord_3097223 prefixEnd_3097223 353414242924542407659697 := by
  unfold tailWord_3097223
  simp only [CollatzResearch.WordTrace]
  refine ⟨112965003258297509420568323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75310002172198339613712215 112965003258297509420568323)
  ·
    refine ⟨169447504887446264130852485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112965003258297509420568323 169447504887446264130852485)
    ·
      refine ⟨31771407166396174524534841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169447504887446264130852485 31771407166396174524534841)
      ·
        refine ⟨23828555374797130893401131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31771407166396174524534841 23828555374797130893401131)
        ·
          refine ⟨35742833062195696340101697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23828555374797130893401131 35742833062195696340101697)
          ·
            refine ⟨26807124796646772255076273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35742833062195696340101697 26807124796646772255076273)
            ·
              refine ⟨20105343597485079191307205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26807124796646772255076273 20105343597485079191307205)
              ·
                refine ⟨3769751924528452348370101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20105343597485079191307205 3769751924528452348370101)
                ·
                  refine ⟨353414242924542407659697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3769751924528452348370101 353414242924542407659697)
                  ·
                    rfl

theorem cell22_3097223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 5].length) (baseStart_3097223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097223 prefixEnd_3097223 := by exact prefixLift 3097223
  have htrace : WordTrace (prefixWord ++ tailWord_3097223) baseStart_3097223 baseEnd_3097223 := by
    simpa [prefixWord, tailWord_3097223, baseEnd_3097223] using wordTrace_append hprefix tailTrace_3097223
  have hstable : (prefixWord ++ tailWord_3097223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097223).length < 2 ^ (prefixWord ++ tailWord_3097223).sum := by decide
  have hdescent : baseEnd_3097223 < baseStart_3097223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097315 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_3097315 : Nat := 118140960795 + 3097315 * 2 ^ 59
def prefixEnd_3097315 : Nat := 4983230072969 + 3 ^ 40 * 3097315 * 2
def baseEnd_3097315 : Nat := 1060274222253769649678809

theorem tailTrace_3097315 : CollatzResearch.WordTrace tailWord_3097315 prefixEnd_3097315 1060274222253769649678809 := by
  unfold tailWord_3097315
  simp only [CollatzResearch.WordTrace]
  refine ⟨112968358773964209132917399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75312239182642806088611599 112968358773964209132917399)
  ·
    refine ⟨169452538160946313699376099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112968358773964209132917399 169452538160946313699376099)
    ·
      refine ⟨254178807241419470549064149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169452538160946313699376099 254178807241419470549064149)
      ·
        refine ⟨5957315794720768840993691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 254178807241419470549064149 5957315794720768840993691)
        ·
          refine ⟨8935973692081153261490537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957315794720768840993691 8935973692081153261490537)
          ·
            refine ⟨6701980269060864946117903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8935973692081153261490537 6701980269060864946117903)
            ·
              refine ⟨10052970403591297419176855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701980269060864946117903 10052970403591297419176855)
              ·
                refine ⟨15079455605386946128765283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10052970403591297419176855 15079455605386946128765283)
                ·
                  refine ⟨22619183408080419193147925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15079455605386946128765283 22619183408080419193147925)
                  ·
                    refine ⟨1060274222253769649678809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22619183408080419193147925 1060274222253769649678809)
                    ·
                      rfl

theorem cell22_3097315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_3097315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097315 prefixEnd_3097315 := by exact prefixLift 3097315
  have htrace : WordTrace (prefixWord ++ tailWord_3097315) baseStart_3097315 baseEnd_3097315 := by
    simpa [prefixWord, tailWord_3097315, baseEnd_3097315] using wordTrace_append hprefix tailTrace_3097315
  have hstable : (prefixWord ++ tailWord_3097315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097315).length < 2 ^ (prefixWord ++ tailWord_3097315).sum := by decide
  have hdescent : baseEnd_3097315 < baseStart_3097315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097396 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3097396 : Nat := 118140960795 + 3097396 * 2 ^ 59
def prefixEnd_3097396 : Nat := 4983230072969 + 3 ^ 40 * 3097396 * 2
def baseEnd_3097396 : Nat := 1060301950209112438403561

theorem tailTrace_3097396 : CollatzResearch.WordTrace tailWord_3097396 prefixEnd_3097396 1060301950209112438403561 := by
  unfold tailWord_3097396
  simp only [CollatzResearch.WordTrace]
  refine ⟨56485656543335379983308021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75314208724447173311077361 56485656543335379983308021)
  ·
    refine ⟨5295530300937691873435127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56485656543335379983308021 5295530300937691873435127)
    ·
      refine ⟨7943295451406537810152691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295530300937691873435127 7943295451406537810152691)
      ·
        refine ⟨11914943177109806715229037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7943295451406537810152691 11914943177109806715229037)
        ·
          refine ⟨4468103691416177518210889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11914943177109806715229037 4468103691416177518210889)
          ·
            refine ⟨3351077768562133138658167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4468103691416177518210889 3351077768562133138658167)
            ·
              refine ⟨5026616652843199707987251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351077768562133138658167 5026616652843199707987251)
              ·
                refine ⟨7539924979264799561980877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026616652843199707987251 7539924979264799561980877)
                ·
                  refine ⟨2827471867224299835742829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7539924979264799561980877 2827471867224299835742829)
                  ·
                    refine ⟨1060301950209112438403561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827471867224299835742829 1060301950209112438403561)
                    ·
                      rfl

theorem cell22_3097396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3097396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097396 prefixEnd_3097396 := by exact prefixLift 3097396
  have htrace : WordTrace (prefixWord ++ tailWord_3097396) baseStart_3097396 baseEnd_3097396 := by
    simpa [prefixWord, tailWord_3097396, baseEnd_3097396] using wordTrace_append hprefix tailTrace_3097396
  have hstable : (prefixWord ++ tailWord_3097396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097396).length < 2 ^ (prefixWord ++ tailWord_3097396).sum := by decide
  have hdescent : baseEnd_3097396 < baseStart_3097396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097409 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 5]
def baseStart_3097409 : Nat := 118140960795 + 3097409 * 2 ^ 59
def prefixEnd_3097409 : Nat := 4983230072969 + 3 ^ 40 * 3097409 * 2
def baseEnd_3097409 : Nat := 353435466791594912609507

theorem tailTrace_3097409 : CollatzResearch.WordTrace tailWord_3097409 prefixEnd_3097409 353435466791594912609507 := by
  unfold tailWord_3097409
  simp only [CollatzResearch.WordTrace]
  refine ⟨112971787235623663186839281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75314524823749108791226187 112971787235623663186839281)
  ·
    refine ⟨84728840426717747390129461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112971787235623663186839281 84728840426717747390129461)
    ·
      refine ⟨7943328790004788817824637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84728840426717747390129461 7943328790004788817824637)
      ·
        refine ⟨2978748296251795806684239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7943328790004788817824637 2978748296251795806684239)
        ·
          refine ⟨4468122444377693710026359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978748296251795806684239 4468122444377693710026359)
          ·
            refine ⟨6702183666566540565039539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468122444377693710026359 6702183666566540565039539)
            ·
              refine ⟨10053275499849810847559309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6702183666566540565039539 10053275499849810847559309)
              ·
                refine ⟨3769978312443679067834741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10053275499849810847559309 3769978312443679067834741)
                ·
                  refine ⟨353435466791594912609507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3769978312443679067834741 353435466791594912609507)
                  ·
                    rfl

theorem cell22_3097409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_3097409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097409 prefixEnd_3097409 := by exact prefixLift 3097409
  have htrace : WordTrace (prefixWord ++ tailWord_3097409) baseStart_3097409 baseEnd_3097409 := by
    simpa [prefixWord, tailWord_3097409, baseEnd_3097409] using wordTrace_append hprefix tailTrace_3097409
  have hstable : (prefixWord ++ tailWord_3097409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097409).length < 2 ^ (prefixWord ++ tailWord_3097409).sum := by decide
  have hdescent : baseEnd_3097409 < baseStart_3097409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097465 : List Nat := [1, 2, 1, 3, 2, 3, 3, 7]
def baseStart_3097465 : Nat := 118140960795 + 3097465 * 2 ^ 59
def prefixEnd_3097465 : Nat := 4983230072969 + 3 ^ 40 * 3097465 * 2
def baseEnd_3097465 : Nat := 117813952257691028714261

theorem tailTrace_3097465 : CollatzResearch.WordTrace tailWord_3097465 prefixEnd_3097465 117813952257691028714261 := by
  unfold tailWord_3097465
  simp only [CollatzResearch.WordTrace]
  refine ⟨112973829723420784750877849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75315886482280523167251899 112973829723420784750877849)
  ·
    refine ⟨84730372292565588563158387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112973829723420784750877849 84730372292565588563158387)
    ·
      refine ⟨127095558438848382844737581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84730372292565588563158387 127095558438848382844737581)
      ·
        refine ⟨47660834414568143566776593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127095558438848382844737581 47660834414568143566776593)
        ·
          refine ⟨35745625810926107675082445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47660834414568143566776593 35745625810926107675082445)
          ·
            refine ⟨13404609679097290378155917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35745625810926107675082445 13404609679097290378155917)
            ·
              refine ⟨5026728629661483891808469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13404609679097290378155917 5026728629661483891808469)
              ·
                refine ⟨117813952257691028714261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5026728629661483891808469 117813952257691028714261)
                ·
                  rfl

theorem cell22_3097465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 7].length) (baseStart_3097465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097465 prefixEnd_3097465 := by exact prefixLift 3097465
  have htrace : WordTrace (prefixWord ++ tailWord_3097465) baseStart_3097465 baseEnd_3097465 := by
    simpa [prefixWord, tailWord_3097465, baseEnd_3097465] using wordTrace_append hprefix tailTrace_3097465
  have hstable : (prefixWord ++ tailWord_3097465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097465).length < 2 ^ (prefixWord ++ tailWord_3097465).sum := by decide
  have hdescent : baseEnd_3097465 < baseStart_3097465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097615 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3097615 : Nat := 118140960795 + 3097615 * 2 ^ 59
def prefixEnd_3097615 : Nat := 4983230072969 + 3 ^ 40 * 3097615 * 2
def baseEnd_3097615 : Nat := 1060376918384668867177889

theorem tailTrace_3097615 : CollatzResearch.WordTrace tailWord_3097615 prefixEnd_3097615 1060376918384668867177889 := by
  unfold tailWord_3097615
  simp only [CollatzResearch.WordTrace]
  refine ⟨112979300672877360368838299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75319533781918240245892199 112979300672877360368838299)
  ·
    refine ⟨169468951009316040553257449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112979300672877360368838299 169468951009316040553257449)
    ·
      refine ⟨127101713256987030414943087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169468951009316040553257449 127101713256987030414943087)
      ·
        refine ⟨190652569885480545622414631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127101713256987030414943087 190652569885480545622414631)
        ·
          refine ⟨285978854828220818433621947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190652569885480545622414631 285978854828220818433621947)
          ·
            refine ⟨428968282242331227650432921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285978854828220818433621947 428968282242331227650432921)
            ·
              refine ⟨321726211681748420737824691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428968282242331227650432921 321726211681748420737824691)
              ·
                refine ⟨482589317522622631106737037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321726211681748420737824691 482589317522622631106737037)
                ·
                  refine ⟨180970994070983486665026389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482589317522622631106737037 180970994070983486665026389)
                  ·
                    refine ⟨1060376918384668867177889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180970994070983486665026389 1060376918384668867177889)
                    ·
                      rfl

theorem cell22_3097615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3097615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097615 prefixEnd_3097615 := by exact prefixLift 3097615
  have htrace : WordTrace (prefixWord ++ tailWord_3097615) baseStart_3097615 baseEnd_3097615 := by
    simpa [prefixWord, tailWord_3097615, baseEnd_3097615] using wordTrace_append hprefix tailTrace_3097615
  have hstable : (prefixWord ++ tailWord_3097615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097615).length < 2 ^ (prefixWord ++ tailWord_3097615).sum := by decide
  have hdescent : baseEnd_3097615 < baseStart_3097615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097621 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_3097621 : Nat := 118140960795 + 3097621 * 2 ^ 59
def prefixEnd_3097621 : Nat := 4983230072969 + 3 ^ 40 * 3097621 * 2
def baseEnd_3097621 : Nat := 1060378972307286851527871

theorem tailTrace_3097621 : CollatzResearch.WordTrace tailWord_3097621 prefixEnd_3097621 1060378972307286851527871 := by
  unfold tailWord_3097621
  simp only [CollatzResearch.WordTrace]
  refine ⟨112979519510855623393556717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75319679673903748929037811 112979519510855623393556717)
  ·
    refine ⟨42367319816570858772583769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112979519510855623393556717 42367319816570858772583769)
    ·
      refine ⟨31775489862428144079437827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42367319816570858772583769 31775489862428144079437827)
      ·
        refine ⟨47663234793642216119156741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31775489862428144079437827 47663234793642216119156741)
        ·
          refine ⟨8936856523807915522341889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47663234793642216119156741 8936856523807915522341889)
          ·
            refine ⟨6702642392855936641756417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8936856523807915522341889 6702642392855936641756417)
            ·
              refine ⟨5026981794641952481317313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6702642392855936641756417 5026981794641952481317313)
              ·
                refine ⟨3770236345981464360987985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5026981794641952481317313 3770236345981464360987985)
                ·
                  refine ⟨2827677259486098270740989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3770236345981464360987985 2827677259486098270740989)
                  ·
                    refine ⟨1060378972307286851527871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827677259486098270740989 1060378972307286851527871)
                    ·
                      rfl

theorem cell22_3097621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_3097621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097621 prefixEnd_3097621 := by exact prefixLift 3097621
  have htrace : WordTrace (prefixWord ++ tailWord_3097621) baseStart_3097621 baseEnd_3097621 := by
    simpa [prefixWord, tailWord_3097621, baseEnd_3097621] using wordTrace_append hprefix tailTrace_3097621
  have hstable : (prefixWord ++ tailWord_3097621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097621).length < 2 ^ (prefixWord ++ tailWord_3097621).sum := by decide
  have hdescent : baseEnd_3097621 < baseStart_3097621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097623 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 4]
def baseStart_3097623 : Nat := 118140960795 + 3097623 * 2 ^ 59
def prefixEnd_3097623 : Nat := 4983230072969 + 3 ^ 40 * 3097623 * 2
def baseEnd_3097623 : Nat := 353459885649386504325955

theorem tailTrace_3097623 : CollatzResearch.WordTrace tailWord_3097623 prefixEnd_3097623 353459885649386504325955 := by
  unfold tailWord_3097623
  simp only [CollatzResearch.WordTrace]
  refine ⟨112979592456848377735129523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75319728304565585156753015 112979592456848377735129523)
  ·
    refine ⟨169469388685272566602694285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112979592456848377735129523 169469388685272566602694285)
    ·
      refine ⟨63551020756977212476010357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169469388685272566602694285 63551020756977212476010357)
      ·
        refine ⟨5957908195966613669625971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63551020756977212476010357 5957908195966613669625971)
        ·
          refine ⟨8936862293949920504438957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957908195966613669625971 8936862293949920504438957)
          ·
            refine ⟨3351323360231220189164609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8936862293949920504438957 3351323360231220189164609)
            ·
              refine ⟨2513492520173415141873457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3351323360231220189164609 2513492520173415141873457)
              ·
                refine ⟨1885119390130061356405093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513492520173415141873457 1885119390130061356405093)
                ·
                  refine ⟨353459885649386504325955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885119390130061356405093 353459885649386504325955)
                  ·
                    rfl

theorem cell22_3097623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 4].length) (baseStart_3097623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097623 prefixEnd_3097623 := by exact prefixLift 3097623
  have htrace : WordTrace (prefixWord ++ tailWord_3097623) baseStart_3097623 baseEnd_3097623 := by
    simpa [prefixWord, tailWord_3097623, baseEnd_3097623] using wordTrace_append hprefix tailTrace_3097623
  have hstable : (prefixWord ++ tailWord_3097623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097623).length < 2 ^ (prefixWord ++ tailWord_3097623).sum := by decide
  have hdescent : baseEnd_3097623 < baseStart_3097623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097634 : List Nat := [3, 3, 1, 1, 1, 5, 1, 7]
def baseStart_3097634 : Nat := 118140960795 + 3097634 * 2 ^ 59
def prefixEnd_3097634 : Nat := 4983230072969 + 3 ^ 40 * 3097634 * 2
def baseEnd_3097634 : Nat := 117820380274773238994759

theorem tailTrace_3097634 : CollatzResearch.WordTrace tailWord_3097634 prefixEnd_3097634 117820380274773238994759 := by
  unfold tailWord_3097634
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244998414952131653444989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75319995773205684409186637 28244998414952131653444989)
  ·
    refine ⟨10591874405607049370041871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28244998414952131653444989 10591874405607049370041871)
    ·
      refine ⟨15887811608410574055062807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10591874405607049370041871 15887811608410574055062807)
      ·
        refine ⟨23831717412615861082594211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887811608410574055062807 23831717412615861082594211)
        ·
          refine ⟨35747576118923791623891317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831717412615861082594211 35747576118923791623891317)
          ·
            refine ⟨3351335261149105464739811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35747576118923791623891317 3351335261149105464739811)
            ·
              refine ⟨5027002891723658197109717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351335261149105464739811 5027002891723658197109717)
              ·
                refine ⟨117820380274773238994759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5027002891723658197109717 117820380274773238994759)
                ·
                  rfl

theorem cell22_3097634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_3097634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097634 prefixEnd_3097634 := by exact prefixLift 3097634
  have htrace : WordTrace (prefixWord ++ tailWord_3097634) baseStart_3097634 baseEnd_3097634 := by
    simpa [prefixWord, tailWord_3097634, baseEnd_3097634] using wordTrace_append hprefix tailTrace_3097634
  have hstable : (prefixWord ++ tailWord_3097634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097634).length < 2 ^ (prefixWord ++ tailWord_3097634).sum := by decide
  have hdescent : baseEnd_3097634 < baseStart_3097634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097649 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_3097649 : Nat := 118140960795 + 3097649 * 2 ^ 59
def prefixEnd_3097649 : Nat := 4983230072969 + 3 ^ 40 * 3097649 * 2
def baseEnd_3097649 : Nat := 1060388557279504111827785

theorem tailTrace_3097649 : CollatzResearch.WordTrace tailWord_3097649 prefixEnd_3097649 1060388557279504111827785 := by
  unfold tailWord_3097649
  simp only [CollatzResearch.WordTrace]
  refine ⟨112980540754754184175576001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75320360503169456117050667 112980540754754184175576001)
  ·
    refine ⟨84735405566065638131682001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112980540754754184175576001 84735405566065638131682001)
    ·
      refine ⟨63551554174549228598761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84735405566065638131682001 63551554174549228598761501)
      ·
        refine ⟨23831832815455960724535563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63551554174549228598761501 23831832815455960724535563)
        ·
          refine ⟨35747749223183941086803345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831832815455960724535563 35747749223183941086803345)
          ·
            refine ⟨26810811917387955815102509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35747749223183941086803345 26810811917387955815102509)
            ·
              refine ⟨10054054469020483430663441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26810811917387955815102509 10054054469020483430663441)
              ·
                refine ⟨7540540851765362572997581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10054054469020483430663441 7540540851765362572997581)
                ·
                  refine ⟨2827702819412010964874093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7540540851765362572997581 2827702819412010964874093)
                  ·
                    refine ⟨1060388557279504111827785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827702819412010964874093 1060388557279504111827785)
                    ·
                      rfl

theorem cell22_3097649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_3097649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097649 prefixEnd_3097649 := by exact prefixLift 3097649
  have htrace : WordTrace (prefixWord ++ tailWord_3097649) baseStart_3097649 baseEnd_3097649 := by
    simpa [prefixWord, tailWord_3097649, baseEnd_3097649] using wordTrace_append hprefix tailTrace_3097649
  have hstable : (prefixWord ++ tailWord_3097649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097649).length < 2 ^ (prefixWord ++ tailWord_3097649).sum := by decide
  have hdescent : baseEnd_3097649 < baseStart_3097649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097717 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_3097717 : Nat := 118140960795 + 3097717 * 2 ^ 59
def prefixEnd_3097717 : Nat := 4983230072969 + 3 ^ 40 * 3097717 * 2
def baseEnd_3097717 : Nat := 1060411835069174601127577

theorem tailTrace_3097717 : CollatzResearch.WordTrace tailWord_3097717 prefixEnd_3097717 1060411835069174601127577 := by
  unfold tailWord_3097717
  simp only [CollatzResearch.WordTrace]
  refine ⟨112983020918507831789051405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75322013945671887859367603 112983020918507831789051405)
  ·
    refine ⟨42368632844440436920894277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112983020918507831789051405 42368632844440436920894277)
    ·
      refine ⟨7944118658332581922667677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42368632844440436920894277 7944118658332581922667677)
      ·
        refine ⟨2979044496874718221000379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7944118658332581922667677 2979044496874718221000379)
        ·
          refine ⟨4468566745312077331500569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979044496874718221000379 4468566745312077331500569)
          ·
            refine ⟨3351425058984057998625427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4468566745312077331500569 3351425058984057998625427)
            ·
              refine ⟨5027137588476086997938141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351425058984057998625427 5027137588476086997938141)
              ·
                refine ⟨1885176595678532624226803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5027137588476086997938141 1885176595678532624226803)
                ·
                  refine ⟨2827764893517798936340205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885176595678532624226803 2827764893517798936340205)
                  ·
                    refine ⟨1060411835069174601127577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827764893517798936340205 1060411835069174601127577)
                    ·
                      rfl

theorem cell22_3097717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_3097717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097717 prefixEnd_3097717 := by exact prefixLift 3097717
  have htrace : WordTrace (prefixWord ++ tailWord_3097717) baseStart_3097717 baseEnd_3097717 := by
    simpa [prefixWord, tailWord_3097717, baseEnd_3097717] using wordTrace_append hprefix tailTrace_3097717
  have hstable : (prefixWord ++ tailWord_3097717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097717).length < 2 ^ (prefixWord ++ tailWord_3097717).sum := by decide
  have hdescent : baseEnd_3097717 < baseStart_3097717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097784 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_3097784 : Nat := 118140960795 + 3097784 * 2 ^ 59
def prefixEnd_3097784 : Nat := 4983230072969 + 3 ^ 40 * 3097784 * 2
def baseEnd_3097784 : Nat := 1060434770538408759702371

theorem tailTrace_3097784 : CollatzResearch.WordTrace tailWord_3097784 prefixEnd_3097784 1060434770538408759702371 := by
  unfold tailWord_3097784
  simp only [CollatzResearch.WordTrace]
  refine ⟨56492732304632551115870203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75323643072843401487826937 56492732304632551115870203)
  ·
    refine ⟨84739098456948826673805305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56492732304632551115870203 84739098456948826673805305)
    ·
      refine ⟨63554323842711620005353979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84739098456948826673805305 63554323842711620005353979)
      ·
        refine ⟨95331485764067430008030969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63554323842711620005353979 95331485764067430008030969)
        ·
          refine ⟨71498614323050572506023227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95331485764067430008030969 71498614323050572506023227)
          ·
            refine ⟨107247921484575858759034841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71498614323050572506023227 107247921484575858759034841)
            ·
              refine ⟨80435941113431894069276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107247921484575858759034841 80435941113431894069276131)
              ·
                refine ⟨120653911670147841103914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80435941113431894069276131 120653911670147841103914197)
                ·
                  refine ⟨2827826054769090025872989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120653911670147841103914197 2827826054769090025872989)
                  ·
                    refine ⟨1060434770538408759702371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827826054769090025872989 1060434770538408759702371)
                    ·
                      rfl

theorem cell22_3097784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_3097784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097784 prefixEnd_3097784 := by exact prefixLift 3097784
  have htrace : WordTrace (prefixWord ++ tailWord_3097784) baseStart_3097784 baseEnd_3097784 := by
    simpa [prefixWord, tailWord_3097784, baseEnd_3097784] using wordTrace_append hprefix tailTrace_3097784
  have hstable : (prefixWord ++ tailWord_3097784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097784).length < 2 ^ (prefixWord ++ tailWord_3097784).sum := by decide
  have hdescent : baseEnd_3097784 < baseStart_3097784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097859 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 6]
def baseStart_3097859 : Nat := 118140960795 + 3097859 * 2 ^ 59
def prefixEnd_3097859 : Nat := 4983230072969 + 3 ^ 40 * 3097859 * 2
def baseEnd_3097859 : Nat := 353486814857044521359047

theorem tailTrace_3097859 : CollatzResearch.WordTrace tailWord_3097859 prefixEnd_3097859 353486814857044521359047 := by
  unfold tailWord_3097859
  simp only [CollatzResearch.WordTrace]
  refine ⟨112988200083993390040720631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75325466722662260027147087 112988200083993390040720631)
  ·
    refine ⟨169482300125990085061080947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112988200083993390040720631 169482300125990085061080947)
    ·
      refine ⟨254223450188985127591621421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169482300125990085061080947 254223450188985127591621421)
      ·
        refine ⟨95333793820869422846858033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254223450188985127591621421 95333793820869422846858033)
        ·
          refine ⟨71500345365652067135143525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95333793820869422846858033 71500345365652067135143525)
          ·
            refine ⟨13406314756059762587839411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71500345365652067135143525 13406314756059762587839411)
            ·
              refine ⟨20109472134089643881759117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406314756059762587839411 20109472134089643881759117)
              ·
                refine ⟨7541052050283616455659669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20109472134089643881759117 7541052050283616455659669)
                ·
                  refine ⟨353486814857044521359047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7541052050283616455659669 353486814857044521359047)
                  ·
                    rfl

theorem cell22_3097859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_3097859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097859 prefixEnd_3097859 := by exact prefixLift 3097859
  have htrace : WordTrace (prefixWord ++ tailWord_3097859) baseStart_3097859 baseEnd_3097859 := by
    simpa [prefixWord, tailWord_3097859, baseEnd_3097859] using wordTrace_append hprefix tailTrace_3097859
  have hstable : (prefixWord ++ tailWord_3097859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097859).length < 2 ^ (prefixWord ++ tailWord_3097859).sum := by decide
  have hdescent : baseEnd_3097859 < baseStart_3097859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097886 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3097886 : Nat := 118140960795 + 3097886 * 2 ^ 59
def prefixEnd_3097886 : Nat := 4983230072969 + 3 ^ 40 * 3097886 * 2
def baseEnd_3097886 : Nat := 1060469687222914493652059

theorem tailTrace_3097886 : CollatzResearch.WordTrace tailWord_3097886 prefixEnd_3097886 1060469687222914493652059 := by
  unfold tailWord_3097886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123648106861946706494189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75326123236597049101302341 14123648106861946706494189)
  ·
    refine ⟨5296368040073230014935321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14123648106861946706494189 5296368040073230014935321)
    ·
      refine ⟨3972276030054922511201491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5296368040073230014935321 3972276030054922511201491)
      ·
        refine ⟨5958414045082383766802237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972276030054922511201491 5958414045082383766802237)
        ·
          refine ⟨2234405266905893912550839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5958414045082383766802237 2234405266905893912550839)
          ·
            refine ⟨3351607900358840868826259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234405266905893912550839 3351607900358840868826259)
            ·
              refine ⟨5027411850538261303239389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351607900358840868826259 5027411850538261303239389)
              ·
                refine ⟨1885279443951847988714771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5027411850538261303239389 1885279443951847988714771)
                ·
                  refine ⟨2827919165927771983072157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885279443951847988714771 2827919165927771983072157)
                  ·
                    refine ⟨1060469687222914493652059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827919165927771983072157 1060469687222914493652059)
                    ·
                      rfl

theorem cell22_3097886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3097886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097886 prefixEnd_3097886 := by exact prefixLift 3097886
  have htrace : WordTrace (prefixWord ++ tailWord_3097886) baseStart_3097886 baseEnd_3097886 := by
    simpa [prefixWord, tailWord_3097886, baseEnd_3097886] using wordTrace_append hprefix tailTrace_3097886
  have hstable : (prefixWord ++ tailWord_3097886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097886).length < 2 ^ (prefixWord ++ tailWord_3097886).sum := by decide
  have hdescent : baseEnd_3097886 < baseStart_3097886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097891 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 4, 3]
def baseStart_3097891 : Nat := 118140960795 + 3097891 * 2 ^ 59
def prefixEnd_3097891 : Nat := 4983230072969 + 3 ^ 40 * 3097891 * 2
def baseEnd_3097891 : Nat := 1060471398825096147277043

theorem tailTrace_3097891 : CollatzResearch.WordTrace tailWord_3097891 prefixEnd_3097891 1060471398825096147277043 := by
  unfold tailWord_3097891
  simp only [CollatzResearch.WordTrace]
  refine ⟨112989367219877459505885527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75326244813251639670590351 112989367219877459505885527)
  ·
    refine ⟨169484050829816189258828291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112989367219877459505885527 169484050829816189258828291)
    ·
      refine ⟨254226076244724283888242437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169484050829816189258828291 254226076244724283888242437)
      ·
        refine ⟨47667389295885803229045457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254226076244724283888242437 47667389295885803229045457)
        ·
          refine ⟨35750541971914352421784093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47667389295885803229045457 35750541971914352421784093)
          ·
            refine ⟨13406453239467882158169035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35750541971914352421784093 13406453239467882158169035)
            ·
              refine ⟨20109679859201823237253553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406453239467882158169035 20109679859201823237253553)
              ·
                refine ⟨15082259894401367427940165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20109679859201823237253553 15082259894401367427940165)
                ·
                  refine ⟨2827923730200256392738781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15082259894401367427940165 2827923730200256392738781)
                  ·
                    refine ⟨1060471398825096147277043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827923730200256392738781 1060471398825096147277043)
                    ·
                      rfl

theorem cell22_3097891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 3].length) (baseStart_3097891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097891 prefixEnd_3097891 := by exact prefixLift 3097891
  have htrace : WordTrace (prefixWord ++ tailWord_3097891) baseStart_3097891 baseEnd_3097891 := by
    simpa [prefixWord, tailWord_3097891, baseEnd_3097891] using wordTrace_append hprefix tailTrace_3097891
  have hstable : (prefixWord ++ tailWord_3097891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097891).length < 2 ^ (prefixWord ++ tailWord_3097891).sum := by decide
  have hdescent : baseEnd_3097891 < baseStart_3097891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097893 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 4]
def baseStart_3097893 : Nat := 118140960795 + 3097893 * 2 ^ 59
def prefixEnd_3097893 : Nat := 4983230072969 + 3 ^ 40 * 3097893 * 2
def baseEnd_3097893 : Nat := 353490694488656269575679

theorem tailTrace_3097893 : CollatzResearch.WordTrace tailWord_3097893 prefixEnd_3097893 353490694488656269575679 := by
  unfold tailWord_3097893
  simp only [CollatzResearch.WordTrace]
  refine ⟨112989440165870213847458333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75326293443913475898305555 112989440165870213847458333)
  ·
    refine ⟨42371040062201330192796875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112989440165870213847458333 42371040062201330192796875)
    ·
      refine ⟨63556560093301995289195313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42371040062201330192796875 63556560093301995289195313)
      ·
        refine ⟨47667420069976496466896485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63556560093301995289195313 47667420069976496466896485)
        ·
          refine ⟨8937641263120593087543091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47667420069976496466896485 8937641263120593087543091)
          ·
            refine ⟨13406461894680889631314637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937641263120593087543091 13406461894680889631314637)
            ·
              refine ⟨5027423210505333611742989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13406461894680889631314637 5027423210505333611742989)
              ·
                refine ⟨1885283703939500104403621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5027423210505333611742989 1885283703939500104403621)
                ·
                  refine ⟨353490694488656269575679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885283703939500104403621 353490694488656269575679)
                  ·
                    rfl

theorem cell22_3097893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_3097893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097893 prefixEnd_3097893 := by exact prefixLift 3097893
  have htrace : WordTrace (prefixWord ++ tailWord_3097893) baseStart_3097893 baseEnd_3097893 := by
    simpa [prefixWord, tailWord_3097893, baseEnd_3097893] using wordTrace_append hprefix tailTrace_3097893
  have hstable : (prefixWord ++ tailWord_3097893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097893).length < 2 ^ (prefixWord ++ tailWord_3097893).sum := by decide
  have hdescent : baseEnd_3097893 < baseStart_3097893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097906 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3097906 : Nat := 118140960795 + 3097906 * 2 ^ 59
def prefixEnd_3097906 : Nat := 4983230072969 + 3 ^ 40 * 3097906 * 2
def baseEnd_3097906 : Nat := 1060476533631641108151997

theorem tailTrace_3097906 : CollatzResearch.WordTrace tailWord_3097906 prefixEnd_3097906 1060476533631641108151997 := by
  unfold tailWord_3097906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28247478578705779266920393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75326609543215411378454381 28247478578705779266920393)
  ·
    refine ⟨21185608934029334450190295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28247478578705779266920393 21185608934029334450190295)
    ·
      refine ⟨31778413401044001675285443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21185608934029334450190295 31778413401044001675285443)
      ·
        refine ⟨47667620101566002512928165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31778413401044001675285443 47667620101566002512928165)
        ·
          refine ⟨8937678769043625471174031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47667620101566002512928165 8937678769043625471174031)
          ·
            refine ⟨13406518153565438206761047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937678769043625471174031 13406518153565438206761047)
            ·
              refine ⟨20109777230348157310141571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406518153565438206761047 20109777230348157310141571)
              ·
                refine ⟨30164665845522235965212357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20109777230348157310141571 30164665845522235965212357)
                ·
                  refine ⟨5655874846035419243477317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30164665845522235965212357 5655874846035419243477317)
                  ·
                    refine ⟨1060476533631641108151997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5655874846035419243477317 1060476533631641108151997)
                    ·
                      rfl

theorem cell22_3097906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3097906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097906 prefixEnd_3097906 := by exact prefixLift 3097906
  have htrace : WordTrace (prefixWord ++ tailWord_3097906) baseStart_3097906 baseEnd_3097906 := by
    simpa [prefixWord, tailWord_3097906, baseEnd_3097906] using wordTrace_append hprefix tailTrace_3097906
  have hstable : (prefixWord ++ tailWord_3097906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097906).length < 2 ^ (prefixWord ++ tailWord_3097906).sum := by decide
  have hdescent : baseEnd_3097906 < baseStart_3097906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097908 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3097908 : Nat := 118140960795 + 3097908 * 2 ^ 59
def prefixEnd_3097908 : Nat := 4983230072969 + 3 ^ 40 * 3097908 * 2
def baseEnd_3097908 : Nat := 1060477218272513769601991

theorem tailTrace_3097908 : CollatzResearch.WordTrace tailWord_3097908 prefixEnd_3097908 1060477218272513769601991 := by
  unfold tailWord_3097908
  simp only [CollatzResearch.WordTrace]
  refine ⟨56494993630407935704627189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75326658173877247606169585 56494993630407935704627189)
  ·
    refine ⟨5296405652850743972308799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56494993630407935704627189 5296405652850743972308799)
    ·
      refine ⟨7944608479276115958463199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296405652850743972308799 7944608479276115958463199)
      ·
        refine ⟨11916912718914173937694799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7944608479276115958463199 11916912718914173937694799)
        ·
          refine ⟨17875369078371260906542199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11916912718914173937694799 17875369078371260906542199)
          ·
            refine ⟨26813053617556891359813299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17875369078371260906542199 26813053617556891359813299)
            ·
              refine ⟨40219580426335337039719949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26813053617556891359813299 40219580426335337039719949)
              ·
                refine ⟨15082342659875751389894981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40219580426335337039719949 15082342659875751389894981)
                ·
                  refine ⟨2827939248726703385605309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15082342659875751389894981 2827939248726703385605309)
                  ·
                    refine ⟨1060477218272513769601991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827939248726703385605309 1060477218272513769601991)
                    ·
                      rfl

theorem cell22_3097908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3097908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097908 prefixEnd_3097908 := by exact prefixLift 3097908
  have htrace : WordTrace (prefixWord ++ tailWord_3097908) baseStart_3097908 baseEnd_3097908 := by
    simpa [prefixWord, tailWord_3097908, baseEnd_3097908] using wordTrace_append hprefix tailTrace_3097908
  have hstable : (prefixWord ++ tailWord_3097908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097908).length < 2 ^ (prefixWord ++ tailWord_3097908).sum := by decide
  have hdescent : baseEnd_3097908 < baseStart_3097908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097921 : List Nat := [1, 2, 5, 2, 1, 1, 1, 9]
def baseStart_3097921 : Nat := 118140960795 + 3097921 * 2 ^ 59
def prefixEnd_3097921 : Nat := 4983230072969 + 3 ^ 40 * 3097921 * 2
def baseEnd_3097921 : Nat := 117831296493131785447439

theorem tailTrace_3097921 : CollatzResearch.WordTrace tailWord_3097921 prefixEnd_3097921 117831296493131785447439 := by
  unfold tailWord_3097921
  simp only [CollatzResearch.WordTrace]
  refine ⟨112990461409768774629477617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75326974273179183086318411 112990461409768774629477617)
  ·
    refine ⟨84742846057326580972108213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112990461409768774629477617 84742846057326580972108213)
    ·
      refine ⟨7944641817874366966135145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84742846057326580972108213 7944641817874366966135145)
      ·
        refine ⟨5958481363405775224601359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7944641817874366966135145 5958481363405775224601359)
        ·
          refine ⟨8937722045108662836902039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958481363405775224601359 8937722045108662836902039)
          ·
            refine ⟨13406583067662994255353059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937722045108662836902039 13406583067662994255353059)
            ·
              refine ⟨20109874601494491383029589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13406583067662994255353059 20109874601494491383029589)
              ·
                refine ⟨117831296493131785447439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20109874601494491383029589 117831296493131785447439)
                ·
                  rfl

theorem cell22_3097921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 9].length) (baseStart_3097921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097921 prefixEnd_3097921 := by exact prefixLift 3097921
  have htrace : WordTrace (prefixWord ++ tailWord_3097921) baseStart_3097921 baseEnd_3097921 := by
    simpa [prefixWord, tailWord_3097921, baseEnd_3097921] using wordTrace_append hprefix tailTrace_3097921
  have hstable : (prefixWord ++ tailWord_3097921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097921).length < 2 ^ (prefixWord ++ tailWord_3097921).sum := by decide
  have hdescent : baseEnd_3097921 < baseStart_3097921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097936 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_3097936 : Nat := 118140960795 + 3097936 * 2 ^ 59
def prefixEnd_3097936 : Nat := 4983230072969 + 3 ^ 40 * 3097936 * 2
def baseEnd_3097936 : Nat := 1060486803244731029901905

theorem tailTrace_3097936 : CollatzResearch.WordTrace tailWord_3097936 prefixEnd_3097936 1060486803244731029901905 := by
  unfold tailWord_3097936
  simp only [CollatzResearch.WordTrace]
  refine ⟨56495504252357216095636831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75327339003142954794182441 56495504252357216095636831)
  ·
    refine ⟨84743256378535824143455247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56495504252357216095636831 84743256378535824143455247)
    ·
      refine ⟨127114884567803736215182871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84743256378535824143455247 127114884567803736215182871)
      ·
        refine ⟨190672326851705604322774307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127114884567803736215182871 190672326851705604322774307)
        ·
          refine ⟨286008490277558406484161461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190672326851705604322774307 286008490277558406484161461)
          ·
            refine ⟨26813295963521100607890137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286008490277558406484161461 26813295963521100607890137)
            ·
              refine ⟨20109971972640825455917603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26813295963521100607890137 20109971972640825455917603)
              ·
                refine ⟨30164957958961238183876405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20109971972640825455917603 30164957958961238183876405)
                ·
                  refine ⟨2827964808652616079738413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30164957958961238183876405 2827964808652616079738413)
                  ·
                    refine ⟨1060486803244731029901905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827964808652616079738413 1060486803244731029901905)
                    ·
                      rfl

theorem cell22_3097936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_3097936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097936 prefixEnd_3097936 := by exact prefixLift 3097936
  have htrace : WordTrace (prefixWord ++ tailWord_3097936) baseStart_3097936 baseEnd_3097936 := by
    simpa [prefixWord, tailWord_3097936, baseEnd_3097936] using wordTrace_append hprefix tailTrace_3097936
  have hstable : (prefixWord ++ tailWord_3097936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097936).length < 2 ^ (prefixWord ++ tailWord_3097936).sum := by decide
  have hdescent : baseEnd_3097936 < baseStart_3097936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097970 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_3097970 : Nat := 118140960795 + 3097970 * 2 ^ 59
def prefixEnd_3097970 : Nat := 4983230072969 + 3 ^ 40 * 3097970 * 2
def baseEnd_3097970 : Nat := 1060498442139566274551801

theorem tailTrace_3097970 : CollatzResearch.WordTrace tailWord_3097970 prefixEnd_3097970 1060498442139566274551801 := by
  unfold tailWord_3097970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248062146647813999502841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75328165724394170665340909 28248062146647813999502841)
  ·
    refine ⟨21186046609985860499627131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28248062146647813999502841 21186046609985860499627131)
    ·
      refine ⟨31779069914978790749440697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21186046609985860499627131 31779069914978790749440697)
      ·
        refine ⟨23834302436234093062080523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31779069914978790749440697 23834302436234093062080523)
        ·
          refine ⟨35751453654351139593120785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23834302436234093062080523 35751453654351139593120785)
          ·
            refine ⟨26813590240763354694840589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35751453654351139593120785 26813590240763354694840589)
            ·
              refine ⟨10055096340286258010565221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26813590240763354694840589 10055096340286258010565221)
              ·
                refine ⟨1885330563803673376980979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10055096340286258010565221 1885330563803673376980979)
                ·
                  refine ⟨2827995845705510065471469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885330563803673376980979 2827995845705510065471469)
                  ·
                    refine ⟨1060498442139566274551801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827995845705510065471469 1060498442139566274551801)
                    ·
                      rfl

theorem cell22_3097970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_3097970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097970 prefixEnd_3097970 := by exact prefixLift 3097970
  have htrace : WordTrace (prefixWord ++ tailWord_3097970) baseStart_3097970 baseEnd_3097970 := by
    simpa [prefixWord, tailWord_3097970, baseEnd_3097970] using wordTrace_append hprefix tailTrace_3097970
  have hstable : (prefixWord ++ tailWord_3097970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097970).length < 2 ^ (prefixWord ++ tailWord_3097970).sum := by decide
  have hdescent : baseEnd_3097970 < baseStart_3097970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097981 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_3097981 : Nat := 118140960795 + 3097981 * 2 ^ 59
def prefixEnd_3097981 : Nat := 4983230072969 + 3 ^ 40 * 3097981 * 2
def baseEnd_3097981 : Nat := 1060502207664365912526767

theorem tailTrace_3097981 : CollatzResearch.WordTrace tailWord_3097981 prefixEnd_3097981 1060502207664365912526767 := by
  unfold tailWord_3097981
  simp only [CollatzResearch.WordTrace]
  refine ⟨112992649789551404876661797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75328433193034269917774531 112992649789551404876661797)
  ·
    refine ⟨21186121835540888414374087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112992649789551404876661797 21186121835540888414374087)
    ·
      refine ⟨31779182753311332621561131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21186121835540888414374087 31779182753311332621561131)
      ·
        refine ⟨47668774129966998932341697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31779182753311332621561131 47668774129966998932341697)
        ·
          refine ⟨35751580597475249199256273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47668774129966998932341697 35751580597475249199256273)
          ·
            refine ⟨26813685448106436899442205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35751580597475249199256273 26813685448106436899442205)
            ·
              refine ⟨10055132043039913837290827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26813685448106436899442205 10055132043039913837290827)
              ·
                refine ⟨15082698064559870755936241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10055132043039913837290827 15082698064559870755936241)
                ·
                  refine ⟨11312023548419903066952181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15082698064559870755936241 11312023548419903066952181)
                  ·
                    refine ⟨1060502207664365912526767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11312023548419903066952181 1060502207664365912526767)
                    ·
                      rfl

theorem cell22_3097981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_3097981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097981 prefixEnd_3097981 := by exact prefixLift 3097981
  have htrace : WordTrace (prefixWord ++ tailWord_3097981) baseStart_3097981 baseEnd_3097981 := by
    simpa [prefixWord, tailWord_3097981, baseEnd_3097981] using wordTrace_append hprefix tailTrace_3097981
  have hstable : (prefixWord ++ tailWord_3097981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097981).length < 2 ^ (prefixWord ++ tailWord_3097981).sum := by decide
  have hdescent : baseEnd_3097981 < baseStart_3097981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3097996 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_3097996 : Nat := 118140960795 + 3097996 * 2 ^ 59
def prefixEnd_3097996 : Nat := 4983230072969 + 3 ^ 40 * 3097996 * 2
def baseEnd_3097996 : Nat := 1060507342470910873401721

theorem tailTrace_3097996 : CollatzResearch.WordTrace tailWord_3097996 prefixEnd_3097996 1060507342470910873401721 := by
  unfold tailWord_3097996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56496598442248531219228921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75328797922998041625638561 56496598442248531219228921)
  ·
    refine ⟨42372448831686398414421691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56496598442248531219228921 42372448831686398414421691)
    ·
      refine ⟨63558673247529597621632537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42372448831686398414421691 63558673247529597621632537)
      ·
        refine ⟨47669004935647198216224403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63558673247529597621632537 47669004935647198216224403)
        ·
          refine ⟨71503507403470797324336605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47669004935647198216224403 71503507403470797324336605)
          ·
            refine ⟨26813815276301548996626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71503507403470797324336605 26813815276301548996626227)
            ·
              refine ⟨40220722914452323494939341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26813815276301548996626227 40220722914452323494939341)
              ·
                refine ⟨15082771092919621310602253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40220722914452323494939341 15082771092919621310602253)
                ·
                  refine ⟨5656039159844857991475845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15082771092919621310602253 5656039159844857991475845)
                  ·
                    refine ⟨1060507342470910873401721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656039159844857991475845 1060507342470910873401721)
                    ·
                      rfl

theorem cell22_3097996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_3097996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3097996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3097996 prefixEnd_3097996 := by exact prefixLift 3097996
  have htrace : WordTrace (prefixWord ++ tailWord_3097996) baseStart_3097996 baseEnd_3097996 := by
    simpa [prefixWord, tailWord_3097996, baseEnd_3097996] using wordTrace_append hprefix tailTrace_3097996
  have hstable : (prefixWord ++ tailWord_3097996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3097996).length < 2 ^ (prefixWord ++ tailWord_3097996).sum := by decide
  have hdescent : baseEnd_3097996 < baseStart_3097996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3097996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098028 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_3098028 : Nat := 118140960795 + 3098028 * 2 ^ 59
def prefixEnd_3098028 : Nat := 4983230072969 + 3 ^ 40 * 3098028 * 2
def baseEnd_3098028 : Nat := 353506098908291152200541

theorem tailTrace_3098028 : CollatzResearch.WordTrace tailWord_3098028 prefixEnd_3098028 353506098908291152200541 := by
  unfold tailWord_3098028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56497182010190565951811369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75329576013587421269081825 56497182010190565951811369)
  ·
    refine ⟨42372886507642924463858527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56497182010190565951811369 42372886507642924463858527)
    ·
      refine ⟨63559329761464386695787791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42372886507642924463858527 63559329761464386695787791)
      ·
        refine ⟨95338994642196580043681687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63559329761464386695787791 95338994642196580043681687)
        ·
          refine ⟨143008491963294870065522531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95338994642196580043681687 143008491963294870065522531)
          ·
            refine ⟨214512737944942305098283797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143008491963294870065522531 214512737944942305098283797)
            ·
              refine ⟨10055284591169170551482053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214512737944942305098283797 10055284591169170551482053)
              ·
                refine ⟨1885365860844219478402885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10055284591169170551482053 1885365860844219478402885)
                ·
                  refine ⟨353506098908291152200541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885365860844219478402885 353506098908291152200541)
                  ·
                    rfl

theorem cell22_3098028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_3098028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098028 prefixEnd_3098028 := by exact prefixLift 3098028
  have htrace : WordTrace (prefixWord ++ tailWord_3098028) baseStart_3098028 baseEnd_3098028 := by
    simpa [prefixWord, tailWord_3098028, baseEnd_3098028] using wordTrace_append hprefix tailTrace_3098028
  have hstable : (prefixWord ++ tailWord_3098028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098028).length < 2 ^ (prefixWord ++ tailWord_3098028).sum := by decide
  have hdescent : baseEnd_3098028 < baseStart_3098028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098056 : List Nat := [2, 1, 3, 1, 3, 1, 3, 8]
def baseStart_3098056 : Nat := 118140960795 + 3098056 * 2 ^ 59
def prefixEnd_3098056 : Nat := 4983230072969 + 3 ^ 40 * 3098056 * 2
def baseEnd_3098056 : Nat := 117836431299676746322393

theorem tailTrace_3098056 : CollatzResearch.WordTrace tailWord_3098056 prefixEnd_3098056 117836431299676746322393 := by
  unfold tailWord_3098056
  simp only [CollatzResearch.WordTrace]
  refine ⟨56497692632139846342821011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75330256842853128457094681 56497692632139846342821011)
  ·
    refine ⟨84746538948209769514231517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56497692632139846342821011 84746538948209769514231517)
    ·
      refine ⟨31779952105578663567836819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84746538948209769514231517 31779952105578663567836819)
      ·
        refine ⟨47669928158367995351755229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31779952105578663567836819 47669928158367995351755229)
        ·
          refine ⟨17876223059387998256908211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47669928158367995351755229 17876223059387998256908211)
          ·
            refine ⟨26814334589081997385362317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17876223059387998256908211 26814334589081997385362317)
            ·
              refine ⟨10055375470905749019510869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26814334589081997385362317 10055375470905749019510869)
              ·
                refine ⟨117836431299676746322393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10055375470905749019510869 117836431299676746322393)
                ·
                  rfl

theorem cell22_3098056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_3098056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098056 prefixEnd_3098056 := by exact prefixLift 3098056
  have htrace : WordTrace (prefixWord ++ tailWord_3098056) baseStart_3098056 baseEnd_3098056 := by
    simpa [prefixWord, tailWord_3098056, baseEnd_3098056] using wordTrace_append hprefix tailTrace_3098056
  have hstable : (prefixWord ++ tailWord_3098056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098056).length < 2 ^ (prefixWord ++ tailWord_3098056).sum := by decide
  have hdescent : baseEnd_3098056 < baseStart_3098056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098163 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 6]
def baseStart_3098163 : Nat := 118140960795 + 3098163 * 2 ^ 59
def prefixEnd_3098163 : Nat := 4983230072969 + 3 ^ 40 * 3098163 * 2
def baseEnd_3098163 : Nat := 353521503327926034825403

theorem tailTrace_3098163 : CollatzResearch.WordTrace tailWord_3098163 prefixEnd_3098163 353521503327926034825403 := by
  unfold tailWord_3098163
  simp only [CollatzResearch.WordTrace]
  refine ⟨112999287874892049959787143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75332858583261366639858095 112999287874892049959787143)
  ·
    refine ⟨169498931812338074939680715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112999287874892049959787143 169498931812338074939680715)
    ·
      refine ⟨254248397718507112409521073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169498931812338074939680715 254248397718507112409521073)
      ·
        refine ⟨190686298288880334307140805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254248397718507112409521073 190686298288880334307140805)
        ·
          refine ⟨35753680929165062682588901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190686298288880334307140805 35753680929165062682588901)
          ·
            refine ⟨6703815174218449252985419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35753680929165062682588901 6703815174218449252985419)
            ·
              refine ⟨10055722761327673879478129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703815174218449252985419 10055722761327673879478129)
              ·
                refine ⟨7541792070995755409608597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10055722761327673879478129 7541792070995755409608597)
                ·
                  refine ⟨353521503327926034825403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7541792070995755409608597 353521503327926034825403)
                  ·
                    rfl

theorem cell22_3098163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_3098163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098163 prefixEnd_3098163 := by exact prefixLift 3098163
  have htrace : WordTrace (prefixWord ++ tailWord_3098163) baseStart_3098163 baseEnd_3098163 := by
    simpa [prefixWord, tailWord_3098163, baseEnd_3098163] using wordTrace_append hprefix tailTrace_3098163
  have hstable : (prefixWord ++ tailWord_3098163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098163).length < 2 ^ (prefixWord ++ tailWord_3098163).sum := by decide
  have hdescent : baseEnd_3098163 < baseStart_3098163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098193 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3098193 : Nat := 118140960795 + 3098193 * 2 ^ 59
def prefixEnd_3098193 : Nat := 4983230072969 + 3 ^ 40 * 3098193 * 2
def baseEnd_3098193 : Nat := 1060574779596868026226117

theorem tailTrace_3098193 : CollatzResearch.WordTrace tailWord_3098193 prefixEnd_3098193 1060574779596868026226117 := by
  unfold tailWord_3098193
  simp only [CollatzResearch.WordTrace]
  refine ⟨113000382064783365083379233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75333588043188910055586155 113000382064783365083379233)
  ·
    refine ⟨84750286548587523812534425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113000382064783365083379233 84750286548587523812534425)
    ·
      refine ⟨63562714911440642859400819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84750286548587523812534425 63562714911440642859400819)
      ·
        refine ⟨95344072367160964289101229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63562714911440642859400819 95344072367160964289101229)
        ·
          refine ⟨35754027137685361608412961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95344072367160964289101229 35754027137685361608412961)
          ·
            refine ⟨26815520353264021206309721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35754027137685361608412961 26815520353264021206309721)
            ·
              refine ⟨20111640264948015904732291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26815520353264021206309721 20111640264948015904732291)
              ·
                refine ⟨30167460397422023857098437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20111640264948015904732291 30167460397422023857098437)
                ·
                  refine ⟨5656398824516629473205957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30167460397422023857098437 5656398824516629473205957)
                  ·
                    refine ⟨1060574779596868026226117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656398824516629473205957 1060574779596868026226117)
                    ·
                      rfl

theorem cell22_3098193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3098193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098193 prefixEnd_3098193 := by exact prefixLift 3098193
  have htrace : WordTrace (prefixWord ++ tailWord_3098193) baseStart_3098193 baseEnd_3098193 := by
    simpa [prefixWord, tailWord_3098193, baseEnd_3098193] using wordTrace_append hprefix tailTrace_3098193
  have hstable : (prefixWord ++ tailWord_3098193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098193).length < 2 ^ (prefixWord ++ tailWord_3098193).sum := by decide
  have hdescent : baseEnd_3098193 < baseStart_3098193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098330 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_3098330 : Nat := 118140960795 + 3098330 * 2 ^ 59
def prefixEnd_3098330 : Nat := 4983230072969 + 3 ^ 40 * 3098330 * 2
def baseEnd_3098330 : Nat := 1060621677496645335550697

theorem tailTrace_3098330 : CollatzResearch.WordTrace tailWord_3098330 prefixEnd_3098330 1060621677496645335550697 := by
  unfold tailWord_3098330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251344716321759370279111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75336919243524691654077629 28251344716321759370279111)
  ·
    refine ⟨42377017074482639055418667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28251344716321759370279111 42377017074482639055418667)
    ·
      refine ⟨63565525611723958583128001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42377017074482639055418667 63565525611723958583128001)
      ·
        refine ⟨47674144208792968937346001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63565525611723958583128001 47674144208792968937346001)
        ·
          refine ⟨35755608156594726703009501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47674144208792968937346001 35755608156594726703009501)
          ·
            refine ⟨13408353058723022513628563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35755608156594726703009501 13408353058723022513628563)
            ·
              refine ⟨20112529588084533770442845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13408353058723022513628563 20112529588084533770442845)
              ·
                refine ⟨7542198595531700163916067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20112529588084533770442845 7542198595531700163916067)
                ·
                  refine ⟨11313297893297550245874101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7542198595531700163916067 11313297893297550245874101)
                  ·
                    refine ⟨1060621677496645335550697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11313297893297550245874101 1060621677496645335550697)
                    ·
                      rfl

theorem cell22_3098330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_3098330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098330 prefixEnd_3098330 := by exact prefixLift 3098330
  have htrace : WordTrace (prefixWord ++ tailWord_3098330) baseStart_3098330 baseEnd_3098330 := by
    simpa [prefixWord, tailWord_3098330, baseEnd_3098330] using wordTrace_append hprefix tailTrace_3098330
  have hstable : (prefixWord ++ tailWord_3098330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098330).length < 2 ^ (prefixWord ++ tailWord_3098330).sum := by decide
  have hdescent : baseEnd_3098330 < baseStart_3098330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098349 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3098349 : Nat := 118140960795 + 3098349 * 2 ^ 59
def prefixEnd_3098349 : Nat := 4983230072969 + 3 ^ 40 * 3098349 * 2
def baseEnd_3098349 : Nat := 353542727194978539775213

theorem tailTrace_3098349 : CollatzResearch.WordTrace tailWord_3098349 prefixEnd_3098349 353542727194978539775213 := by
  unfold tailWord_3098349
  simp only [CollatzResearch.WordTrace]
  refine ⟨113006071852218203726058101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75337381234812135817372067 113006071852218203726058101)
  ·
    refine ⟨10594319236145456599317947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113006071852218203726058101 10594319236145456599317947)
    ·
      refine ⟨15891478854218184898976921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10594319236145456599317947 15891478854218184898976921)
      ·
        refine ⟨11918609140663638674232691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15891478854218184898976921 11918609140663638674232691)
        ·
          refine ⟨17877913710995458011349037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11918609140663638674232691 17877913710995458011349037)
          ·
            refine ⟨6704217641623296754255889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17877913710995458011349037 6704217641623296754255889)
            ·
              refine ⟨5028163231217472565691917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6704217641623296754255889 5028163231217472565691917)
              ·
                refine ⟨1885561211706552212134469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5028163231217472565691917 1885561211706552212134469)
                ·
                  refine ⟨353542727194978539775213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885561211706552212134469 353542727194978539775213)
                  ·
                    rfl

theorem cell22_3098349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3098349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098349 prefixEnd_3098349 := by exact prefixLift 3098349
  have htrace : WordTrace (prefixWord ++ tailWord_3098349) baseStart_3098349 baseEnd_3098349 := by
    simpa [prefixWord, tailWord_3098349, baseEnd_3098349] using wordTrace_append hprefix tailTrace_3098349
  have hstable : (prefixWord ++ tailWord_3098349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098349).length < 2 ^ (prefixWord ++ tailWord_3098349).sum := by decide
  have hdescent : baseEnd_3098349 < baseStart_3098349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098392 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_3098392 : Nat := 118140960795 + 3098392 * 2 ^ 59
def prefixEnd_3098392 : Nat := 4983230072969 + 3 ^ 40 * 3098392 * 2
def baseEnd_3098392 : Nat := 1060642901363697840500507

theorem tailTrace_3098392 : CollatzResearch.WordTrace tailWord_3098392 prefixEnd_3098392 1060642901363697840500507 := by
  unfold tailWord_3098392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56503820095531211034936715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75338426794041614713248953 56503820095531211034936715)
  ·
    refine ⟨84755730143296816552405073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56503820095531211034936715 84755730143296816552405073)
    ·
      refine ⟨63566797607472612414303805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84755730143296816552405073 63566797607472612414303805)
      ·
        refine ⟨23837549102802229655363927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63566797607472612414303805 23837549102802229655363927)
        ·
          refine ⟨35756323654203344483045891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23837549102802229655363927 35756323654203344483045891)
          ·
            refine ⟨53634485481305016724568837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35756323654203344483045891 53634485481305016724568837)
            ·
              refine ⟨10056466027744690635856657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53634485481305016724568837 10056466027744690635856657)
              ·
                refine ⟨7542349520808517976892493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10056466027744690635856657 7542349520808517976892493)
                ·
                  refine ⟨2828381070303194241334685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7542349520808517976892493 2828381070303194241334685)
                  ·
                    refine ⟨1060642901363697840500507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828381070303194241334685 1060642901363697840500507)
                    ·
                      rfl

theorem cell22_3098392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_3098392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098392 prefixEnd_3098392 := by exact prefixLift 3098392
  have htrace : WordTrace (prefixWord ++ tailWord_3098392) baseStart_3098392 baseEnd_3098392 := by
    simpa [prefixWord, tailWord_3098392, baseEnd_3098392] using wordTrace_append hprefix tailTrace_3098392
  have hstable : (prefixWord ++ tailWord_3098392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098392).length < 2 ^ (prefixWord ++ tailWord_3098392).sum := by decide
  have hdescent : baseEnd_3098392 < baseStart_3098392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098405 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 7]
def baseStart_3098405 : Nat := 118140960795 + 3098405 * 2 ^ 59
def prefixEnd_3098405 : Nat := 4983230072969 + 3 ^ 40 * 3098405 * 2
def baseEnd_3098405 : Nat := 353549117176456713308489

theorem tailTrace_3098405 : CollatzResearch.WordTrace tailWord_3098405 prefixEnd_3098405 353549117176456713308489 := by
  unfold tailWord_3098405
  simp only [CollatzResearch.WordTrace]
  refine ⟨113008114340015325290096669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75338742893343550193397779 113008114340015325290096669)
  ·
    refine ⟨42378042877505746983786251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113008114340015325290096669 42378042877505746983786251)
    ·
      refine ⟨63567064316258620475679377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42378042877505746983786251 63567064316258620475679377)
      ·
        refine ⟨47675298237193965356759533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63567064316258620475679377 47675298237193965356759533)
        ·
          refine ⟨17878236838947737008784825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47675298237193965356759533 17878236838947737008784825)
          ·
            refine ⟨13408677629210802756588619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17878236838947737008784825 13408677629210802756588619)
            ·
              refine ⟨20113016443816204134882929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13408677629210802756588619 20113016443816204134882929)
              ·
                refine ⟨15084762332862153101162197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20113016443816204134882929 15084762332862153101162197)
                ·
                  refine ⟨353549117176456713308489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15084762332862153101162197 353549117176456713308489)
                  ·
                    rfl

theorem cell22_3098405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_3098405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098405 prefixEnd_3098405 := by exact prefixLift 3098405
  have htrace : WordTrace (prefixWord ++ tailWord_3098405) baseStart_3098405 baseEnd_3098405 := by
    simpa [prefixWord, tailWord_3098405, baseEnd_3098405] using wordTrace_append hprefix tailTrace_3098405
  have hstable : (prefixWord ++ tailWord_3098405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098405).length < 2 ^ (prefixWord ++ tailWord_3098405).sum := by decide
  have hdescent : baseEnd_3098405 < baseStart_3098405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098480 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_3098480 : Nat := 118140960795 + 3098480 * 2 ^ 59
def prefixEnd_3098480 : Nat := 4983230072969 + 3 ^ 40 * 3098480 * 2
def baseEnd_3098480 : Nat := 1060673025562094944300237

theorem tailTrace_3098480 : CollatzResearch.WordTrace tailWord_3098480 prefixEnd_3098480 1060673025562094944300237 := by
  unfold tailWord_3098480
  simp only [CollatzResearch.WordTrace]
  refine ⟨56505424907371806549538447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75340566543162408732717929 56505424907371806549538447)
  ·
    refine ⟨84758137361057709824307671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56505424907371806549538447 84758137361057709824307671)
    ·
      refine ⟨127137206041586564736461507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84758137361057709824307671 127137206041586564736461507)
      ·
        refine ⟨190705809062379847104692261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127137206041586564736461507 190705809062379847104692261)
        ·
          refine ⟨35757339199196221332129799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190705809062379847104692261 35757339199196221332129799)
          ·
            refine ⟨53636008798794331998194699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35757339199196221332129799 53636008798794331998194699)
            ·
              refine ⟨80454013198191497997292049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53636008798794331998194699 80454013198191497997292049)
              ·
                refine ⟨60340509898643623497969037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80454013198191497997292049 60340509898643623497969037)
                ·
                  refine ⟨22627691211991358811738389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60340509898643623497969037 22627691211991358811738389)
                  ·
                    refine ⟨1060673025562094944300237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22627691211991358811738389 1060673025562094944300237)
                    ·
                      rfl

theorem cell22_3098480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_3098480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098480 prefixEnd_3098480 := by exact prefixLift 3098480
  have htrace : WordTrace (prefixWord ++ tailWord_3098480) baseStart_3098480 baseEnd_3098480 := by
    simpa [prefixWord, tailWord_3098480, baseEnd_3098480] using wordTrace_append hprefix tailTrace_3098480
  have hstable : (prefixWord ++ tailWord_3098480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098480).length < 2 ^ (prefixWord ++ tailWord_3098480).sum := by decide
  have hdescent : baseEnd_3098480 < baseStart_3098480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098499 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 2, 3]
def baseStart_3098499 : Nat := 118140960795 + 3098499 * 2 ^ 59
def prefixEnd_3098499 : Nat := 4983230072969 + 3 ^ 40 * 3098499 * 2
def baseEnd_3098499 : Nat := 1060679529650385228075179

theorem tailTrace_3098499 : CollatzResearch.WordTrace tailWord_3098499 prefixEnd_3098499 1060679529650385228075179 := by
  unfold tailWord_3098499
  simp only [CollatzResearch.WordTrace]
  refine ⟨113011542801674779344018551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75341028534449852896012367 113011542801674779344018551)
  ·
    refine ⟨169517314202512169016027827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113011542801674779344018551 169517314202512169016027827)
    ·
      refine ⟨254275971303768253524041741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169517314202512169016027827 254275971303768253524041741)
      ·
        refine ⟨95353489238913095071515653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254275971303768253524041741 95353489238913095071515653)
        ·
          refine ⟨17878779232296205325909185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95353489238913095071515653 17878779232296205325909185)
          ·
            refine ⟨13409084424222153994431889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17878779232296205325909185 13409084424222153994431889)
            ·
              refine ⟨10056813318166615495823917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13409084424222153994431889 10056813318166615495823917)
              ·
                refine ⟨3771304994312480810933969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10056813318166615495823917 3771304994312480810933969)
                ·
                  refine ⟨2828478745734360608200477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3771304994312480810933969 2828478745734360608200477)
                  ·
                    refine ⟨1060679529650385228075179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828478745734360608200477 1060679529650385228075179)
                    ·
                      rfl

theorem cell22_3098499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 3].length) (baseStart_3098499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098499 prefixEnd_3098499 := by exact prefixLift 3098499
  have htrace : WordTrace (prefixWord ++ tailWord_3098499) baseStart_3098499 baseEnd_3098499 := by
    simpa [prefixWord, tailWord_3098499, baseEnd_3098499] using wordTrace_append hprefix tailTrace_3098499
  have hstable : (prefixWord ++ tailWord_3098499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098499).length < 2 ^ (prefixWord ++ tailWord_3098499).sum := by decide
  have hdescent : baseEnd_3098499 < baseStart_3098499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098514 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3098514 : Nat := 118140960795 + 3098514 * 2 ^ 59
def prefixEnd_3098514 : Nat := 4983230072969 + 3 ^ 40 * 3098514 * 2
def baseEnd_3098514 : Nat := 1060684664456930188950133

theorem tailTrace_3098514 : CollatzResearch.WordTrace tailWord_3098514 prefixEnd_3098514 1060684664456930188950133 := by
  unfold tailWord_3098514
  simp only [CollatzResearch.WordTrace]
  refine ⟨28253022474155109226453649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75341393264413624603876397 28253022474155109226453649)
  ·
    refine ⟨21189766855616331919840237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28253022474155109226453649 21189766855616331919840237)
    ·
      refine ⟨7946162570856124469940089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21189766855616331919840237 7946162570856124469940089)
      ·
        refine ⟨5959621928142093352455067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7946162570856124469940089 5959621928142093352455067)
        ·
          refine ⟨8939432892213140028682601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5959621928142093352455067 8939432892213140028682601)
          ·
            refine ⟨6704574669159855021511951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8939432892213140028682601 6704574669159855021511951)
            ·
              refine ⟨10056862003739782532267927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704574669159855021511951 10056862003739782532267927)
              ·
                refine ⟨15085293005609673798401891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10056862003739782532267927 15085293005609673798401891)
                ·
                  refine ⟨22627939508414510697602837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15085293005609673798401891 22627939508414510697602837)
                  ·
                    refine ⟨1060684664456930188950133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22627939508414510697602837 1060684664456930188950133)
                    ·
                      rfl

theorem cell22_3098514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3098514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098514 prefixEnd_3098514 := by exact prefixLift 3098514
  have htrace : WordTrace (prefixWord ++ tailWord_3098514) baseStart_3098514 baseEnd_3098514 := by
    simpa [prefixWord, tailWord_3098514, baseEnd_3098514] using wordTrace_append hprefix tailTrace_3098514
  have hstable : (prefixWord ++ tailWord_3098514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098514).length < 2 ^ (prefixWord ++ tailWord_3098514).sum := by decide
  have hdescent : baseEnd_3098514 < baseStart_3098514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098520 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 1, 4]
def baseStart_3098520 : Nat := 118140960795 + 3098520 * 2 ^ 59
def prefixEnd_3098520 : Nat := 4983230072969 + 3 ^ 40 * 3098520 * 2
def baseEnd_3098520 : Nat := 1060686718379548173300115

theorem tailTrace_3098520 : CollatzResearch.WordTrace tailWord_3098520 prefixEnd_3098520 1060686718379548173300115 := by
  unfold tailWord_3098520
  simp only [CollatzResearch.WordTrace]
  refine ⟨56506154367299349965266507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75341539156399133287022009 56506154367299349965266507)
  ·
    refine ⟨84759231550949024947899761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56506154367299349965266507 84759231550949024947899761)
    ·
      refine ⟨63569423663211768710924821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84759231550949024947899761 63569423663211768710924821)
      ·
        refine ⟨2979816734213051658324601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63569423663211768710924821 2979816734213051658324601)
        ·
          refine ⟨2234862550659788743743451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2979816734213051658324601 2234862550659788743743451)
          ·
            refine ⟨3352293825989683115615177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234862550659788743743451 3352293825989683115615177)
            ·
              refine ⟨2514220369492262336711383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352293825989683115615177 2514220369492262336711383)
              ·
                refine ⟨3771330554238393505067075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514220369492262336711383 3771330554238393505067075)
                ·
                  refine ⟨5656995831357590257600613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771330554238393505067075 5656995831357590257600613)
                  ·
                    refine ⟨1060686718379548173300115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5656995831357590257600613 1060686718379548173300115)
                    ·
                      rfl

theorem cell22_3098520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_3098520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098520 prefixEnd_3098520 := by exact prefixLift 3098520
  have htrace : WordTrace (prefixWord ++ tailWord_3098520) baseStart_3098520 baseEnd_3098520 := by
    simpa [prefixWord, tailWord_3098520, baseEnd_3098520] using wordTrace_append hprefix tailTrace_3098520
  have hstable : (prefixWord ++ tailWord_3098520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098520).length < 2 ^ (prefixWord ++ tailWord_3098520).sum := by decide
  have hdescent : baseEnd_3098520 < baseStart_3098520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098647 : List Nat := [1, 1, 3, 5, 12]
def baseStart_3098647 : Nat := 118140960795 + 3098647 * 2 ^ 59
def prefixEnd_3098647 : Nat := 4983230072969 + 3 ^ 40 * 3098647 * 2
def baseEnd_3098647 : Nat := 4365144827468980145575

theorem tailTrace_3098647 : CollatzResearch.WordTrace tailWord_3098647 prefixEnd_3098647 4365144827468980145575 := by
  unfold tailWord_3098647
  simp only [CollatzResearch.WordTrace]
  refine ⟨113016940805138600620406195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75344627203425733746937463 113016940805138600620406195)
  ·
    refine ⟨169525411207707900930609293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113016940805138600620406195 169525411207707900930609293)
    ·
      refine ⟨63572029202890462848978485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169525411207707900930609293 63572029202890462848978485)
      ·
        refine ⟨5959877737770980892091733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63572029202890462848978485 5959877737770980892091733)
        ·
          refine ⟨4365144827468980145575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5959877737770980892091733 4365144827468980145575)
          ·
            rfl

theorem cell22_3098647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 12].length) (baseStart_3098647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098647 prefixEnd_3098647 := by exact prefixLift 3098647
  have htrace : WordTrace (prefixWord ++ tailWord_3098647) baseStart_3098647 baseEnd_3098647 := by
    simpa [prefixWord, tailWord_3098647, baseEnd_3098647] using wordTrace_append hprefix tailTrace_3098647
  have hstable : (prefixWord ++ tailWord_3098647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098647).length < 2 ^ (prefixWord ++ tailWord_3098647).sum := by decide
  have hdescent : baseEnd_3098647 < baseStart_3098647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098653 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 4]
def baseStart_3098653 : Nat := 118140960795 + 3098653 * 2 ^ 59
def prefixEnd_3098653 : Nat := 4983230072969 + 3 ^ 40 * 3098653 * 2
def baseEnd_3098653 : Nat := 353577415665860053241569

theorem tailTrace_3098653 : CollatzResearch.WordTrace tailWord_3098653 prefixEnd_3098653 353577415665860053241569 := by
  unfold tailWord_3098653
  simp only [CollatzResearch.WordTrace]
  refine ⟨113017159643116863645124613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75344773095411242430083075 113017159643116863645124613)
  ·
    refine ⟨21190717433084411933460865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113017159643116863645124613 21190717433084411933460865)
    ·
      refine ⟨15893038074813308950095649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21190717433084411933460865 15893038074813308950095649)
      ·
        refine ⟨11919778556109981712571737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15893038074813308950095649 11919778556109981712571737)
        ·
          refine ⟨8939833917082486284428803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11919778556109981712571737 8939833917082486284428803)
          ·
            refine ⟨13409750875623729426643205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8939833917082486284428803 13409750875623729426643205)
            ·
              refine ⟨2514328289179449267495601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13409750875623729426643205 2514328289179449267495601)
              ·
                refine ⟨1885746216884586950621701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514328289179449267495601 1885746216884586950621701)
                ·
                  refine ⟨353577415665860053241569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885746216884586950621701 353577415665860053241569)
                  ·
                    rfl

theorem cell22_3098653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_3098653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098653 prefixEnd_3098653 := by exact prefixLift 3098653
  have htrace : WordTrace (prefixWord ++ tailWord_3098653) baseStart_3098653 baseEnd_3098653 := by
    simpa [prefixWord, tailWord_3098653, baseEnd_3098653] using wordTrace_append hprefix tailTrace_3098653
  have hstable : (prefixWord ++ tailWord_3098653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098653).length < 2 ^ (prefixWord ++ tailWord_3098653).sum := by decide
  have hdescent : baseEnd_3098653 < baseStart_3098653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098679 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 5, 3]
def baseStart_3098679 : Nat := 118140960795 + 3098679 * 2 ^ 59
def prefixEnd_3098679 : Nat := 4983230072969 + 3 ^ 40 * 3098679 * 2
def baseEnd_3098679 : Nat := 1060741147328924758574627

theorem tailTrace_3098679 : CollatzResearch.WordTrace tailWord_3098679 prefixEnd_3098679 1060741147328924758574627 := by
  unfold tailWord_3098679
  simp only [CollatzResearch.WordTrace]
  refine ⟨113018107941022670085571091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75345405294015113390380727 113018107941022670085571091)
  ·
    refine ⟨169527161911534005128356637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113018107941022670085571091 169527161911534005128356637)
    ·
      refine ⟨63572685716825251923133739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169527161911534005128356637 63572685716825251923133739)
      ·
        refine ⟨95359028575237877884700609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63572685716825251923133739 95359028575237877884700609)
        ·
          refine ⟨71519271431428408413525457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95359028575237877884700609 71519271431428408413525457)
          ·
            refine ⟨53639453573571306310144093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71519271431428408413525457 53639453573571306310144093)
            ·
              refine ⟨20114795090089239866304035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53639453573571306310144093 20114795090089239866304035)
              ·
                refine ⟨30172192635133859799456053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20114795090089239866304035 30172192635133859799456053)
                ·
                  refine ⟨2828643059543799356199005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30172192635133859799456053 2828643059543799356199005)
                  ·
                    refine ⟨1060741147328924758574627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828643059543799356199005 1060741147328924758574627)
                    ·
                      rfl

theorem cell22_3098679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_3098679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098679 prefixEnd_3098679 := by exact prefixLift 3098679
  have htrace : WordTrace (prefixWord ++ tailWord_3098679) baseStart_3098679 baseEnd_3098679 := by
    simpa [prefixWord, tailWord_3098679, baseEnd_3098679] using wordTrace_append hprefix tailTrace_3098679
  have hstable : (prefixWord ++ tailWord_3098679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098679).length < 2 ^ (prefixWord ++ tailWord_3098679).sum := by decide
  have hdescent : baseEnd_3098679 < baseStart_3098679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098681 : List Nat := [1, 2, 1, 5, 3, 1, 3, 6]
def baseStart_3098681 : Nat := 118140960795 + 3098681 * 2 ^ 59
def prefixEnd_3098681 : Nat := 4983230072969 + 3 ^ 40 * 3098681 * 2
def baseEnd_3098681 : Nat := 117860203552199713336069

theorem tailTrace_3098681 : CollatzResearch.WordTrace tailWord_3098681 prefixEnd_3098681 117860203552199713336069 := by
  unfold tailWord_3098681
  simp only [CollatzResearch.WordTrace]
  refine ⟨113018180887015424427143897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75345453924676949618095931 113018180887015424427143897)
  ·
    refine ⟨84763635665261568320357923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113018180887015424427143897 84763635665261568320357923)
    ·
      refine ⟨127145453497892352480536885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84763635665261568320357923 127145453497892352480536885)
      ·
        refine ⟨11919886265427408045050333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127145453497892352480536885 11919886265427408045050333)
        ·
          refine ⟨4469957349535278016893875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11919886265427408045050333 4469957349535278016893875)
          ·
            refine ⟨6704936024302917025340813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469957349535278016893875 6704936024302917025340813)
            ·
              refine ⟨2514351009113593884502805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6704936024302917025340813 2514351009113593884502805)
              ·
                refine ⟨117860203552199713336069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2514351009113593884502805 117860203552199713336069)
                ·
                  rfl

theorem cell22_3098681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 6].length) (baseStart_3098681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098681 prefixEnd_3098681 := by exact prefixLift 3098681
  have htrace : WordTrace (prefixWord ++ tailWord_3098681) baseStart_3098681 baseEnd_3098681 := by
    simpa [prefixWord, tailWord_3098681, baseEnd_3098681] using wordTrace_append hprefix tailTrace_3098681
  have hstable : (prefixWord ++ tailWord_3098681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098681).length < 2 ^ (prefixWord ++ tailWord_3098681).sum := by decide
  have hdescent : baseEnd_3098681 < baseStart_3098681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098709 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 7]
def baseStart_3098709 : Nat := 118140960795 + 3098709 * 2 ^ 59
def prefixEnd_3098709 : Nat := 4983230072969 + 3 ^ 40 * 3098709 * 2
def baseEnd_3098709 : Nat := 353583805647338226774845

theorem tailTrace_3098709 : CollatzResearch.WordTrace tailWord_3098709 prefixEnd_3098709 353583805647338226774845 := by
  unfold tailWord_3098709
  simp only [CollatzResearch.WordTrace]
  refine ⟨113019202130913985209163181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75346134753942656806108787 113019202130913985209163181)
  ·
    refine ⟨42382200799092744453436193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113019202130913985209163181 42382200799092744453436193)
    ·
      refine ⟨31786650599319558340077145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42382200799092744453436193 31786650599319558340077145)
      ·
        refine ⟨23839987949489668755057859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31786650599319558340077145 23839987949489668755057859)
        ·
          refine ⟨35759981924234503132586789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23839987949489668755057859 35759981924234503132586789)
          ·
            refine ⟨6704996610793969337360023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35759981924234503132586789 6704996610793969337360023)
            ·
              refine ⟨10057494916190954006040035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6704996610793969337360023 10057494916190954006040035)
              ·
                refine ⟨15086242374286431009060053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10057494916190954006040035 15086242374286431009060053)
                ·
                  refine ⟨353583805647338226774845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15086242374286431009060053 353583805647338226774845)
                  ·
                    rfl

theorem cell22_3098709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_3098709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098709 prefixEnd_3098709 := by exact prefixLift 3098709
  have htrace : WordTrace (prefixWord ++ tailWord_3098709) baseStart_3098709 baseEnd_3098709 := by
    simpa [prefixWord, tailWord_3098709, baseEnd_3098709] using wordTrace_append hprefix tailTrace_3098709
  have hstable : (prefixWord ++ tailWord_3098709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098709).length < 2 ^ (prefixWord ++ tailWord_3098709).sum := by decide
  have hdescent : baseEnd_3098709 < baseStart_3098709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098724 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_3098724 : Nat := 118140960795 + 3098724 * 2 ^ 59
def prefixEnd_3098724 : Nat := 4983230072969 + 3 ^ 40 * 3098724 * 2
def baseEnd_3098724 : Nat := 1060756551748559641199489

theorem tailTrace_3098724 : CollatzResearch.WordTrace tailWord_3098724 prefixEnd_3098724 1060756551748559641199489 := by
  unfold tailWord_3098724
  simp only [CollatzResearch.WordTrace]
  refine ⟨56509874612929821385479613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75346499483906428513972817 56509874612929821385479613)
  ·
    refine ⟨21191202979848683019554855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56509874612929821385479613 21191202979848683019554855)
    ·
      refine ⟨31786804469773024529332283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21191202979848683019554855 31786804469773024529332283)
      ·
        refine ⟨47680206704659536793998425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31786804469773024529332283 47680206704659536793998425)
        ·
          refine ⟨35760155028494652595498819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47680206704659536793998425 35760155028494652595498819)
          ·
            refine ⟨53640232542741978893248229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35760155028494652595498819 53640232542741978893248229)
            ·
              refine ⟨10057543601764121042484043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53640232542741978893248229 10057543601764121042484043)
              ·
                refine ⟨15086315402646181563726065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10057543601764121042484043 15086315402646181563726065)
                ·
                  refine ⟨11314736551984636172794549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15086315402646181563726065 11314736551984636172794549)
                  ·
                    refine ⟨1060756551748559641199489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11314736551984636172794549 1060756551748559641199489)
                    ·
                      rfl

theorem cell22_3098724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_3098724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098724 prefixEnd_3098724 := by exact prefixLift 3098724
  have htrace : WordTrace (prefixWord ++ tailWord_3098724) baseStart_3098724 baseEnd_3098724 := by
    simpa [prefixWord, tailWord_3098724, baseEnd_3098724] using wordTrace_append hprefix tailTrace_3098724
  have hstable : (prefixWord ++ tailWord_3098724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098724).length < 2 ^ (prefixWord ++ tailWord_3098724).sum := by decide
  have hdescent : baseEnd_3098724 < baseStart_3098724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098756 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3098756 : Nat := 118140960795 + 3098756 * 2 ^ 59
def prefixEnd_3098756 : Nat := 4983230072969 + 3 ^ 40 * 3098756 * 2
def baseEnd_3098756 : Nat := 1060767506002522224399391

theorem tailTrace_3098756 : CollatzResearch.WordTrace tailWord_3098756 prefixEnd_3098756 1060767506002522224399391 := by
  unfold tailWord_3098756
  simp only [CollatzResearch.WordTrace]
  refine ⟨56510458180871856118062061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75347277574495808157416081 56510458180871856118062061)
  ·
    refine ⟨21191421817826946044273273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56510458180871856118062061 21191421817826946044273273)
    ·
      refine ⟨15893566363370209533204955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21191421817826946044273273 15893566363370209533204955)
      ·
        refine ⟨23840349545055314299807433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15893566363370209533204955 23840349545055314299807433)
        ·
          refine ⟨17880262158791485724855575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23840349545055314299807433 17880262158791485724855575)
          ·
            refine ⟨26820393238187228587283363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17880262158791485724855575 26820393238187228587283363)
            ·
              refine ⟨40230589857280842880925045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26820393238187228587283363 40230589857280842880925045)
              ·
                refine ⟨3771617799120079020086723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40230589857280842880925045 3771617799120079020086723)
                ·
                  refine ⟨5657426698680118530130085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771617799120079020086723 5657426698680118530130085)
                  ·
                    refine ⟨1060767506002522224399391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5657426698680118530130085 1060767506002522224399391)
                    ·
                      rfl

theorem cell22_3098756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3098756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098756 prefixEnd_3098756 := by exact prefixLift 3098756
  have htrace : WordTrace (prefixWord ++ tailWord_3098756) baseStart_3098756 baseEnd_3098756 := by
    simpa [prefixWord, tailWord_3098756, baseEnd_3098756] using wordTrace_append hprefix tailTrace_3098756
  have hstable : (prefixWord ++ tailWord_3098756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098756).length < 2 ^ (prefixWord ++ tailWord_3098756).sum := by decide
  have hdescent : baseEnd_3098756 < baseStart_3098756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098820 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3098820 : Nat := 118140960795 + 3098820 * 2 ^ 59
def prefixEnd_3098820 : Nat := 4983230072969 + 3 ^ 40 * 3098820 * 2
def baseEnd_3098820 : Nat := 1060789414510447390799195

theorem tailTrace_3098820 : CollatzResearch.WordTrace tailWord_3098820 prefixEnd_3098820 1060789414510447390799195 := by
  unfold tailWord_3098820
  simp only [CollatzResearch.WordTrace]
  refine ⟨56511625316755925583226957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75348833755674567444302609 56511625316755925583226957)
  ·
    refine ⟨21191859493783472093710109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56511625316755925583226957 21191859493783472093710109)
    ·
      refine ⟨7946947310168802035141291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21191859493783472093710109 7946947310168802035141291)
      ·
        refine ⟨11920420965253203052711937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7946947310168802035141291 11920420965253203052711937)
        ·
          refine ⟨8940315723939902289533953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11920420965253203052711937 8940315723939902289533953)
          ·
            refine ⟨6705236792954926717150465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8940315723939902289533953 6705236792954926717150465)
            ·
              refine ⟨5028927594716195037862849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705236792954926717150465 5028927594716195037862849)
              ·
                refine ⟨3771695696037146278397137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028927594716195037862849 3771695696037146278397137)
                ·
                  refine ⟨2828771772027859708797853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3771695696037146278397137 2828771772027859708797853)
                  ·
                    refine ⟨1060789414510447390799195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828771772027859708797853 1060789414510447390799195)
                    ·
                      rfl

theorem cell22_3098820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3098820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098820 prefixEnd_3098820 := by exact prefixLift 3098820
  have htrace : WordTrace (prefixWord ++ tailWord_3098820) baseStart_3098820 baseEnd_3098820 := by
    simpa [prefixWord, tailWord_3098820, baseEnd_3098820] using wordTrace_append hprefix tailTrace_3098820
  have hstable : (prefixWord ++ tailWord_3098820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098820).length < 2 ^ (prefixWord ++ tailWord_3098820).sum := by decide
  have hdescent : baseEnd_3098820 < baseStart_3098820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098831 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 3, 3]
def baseStart_3098831 : Nat := 118140960795 + 3098831 * 2 ^ 59
def prefixEnd_3098831 : Nat := 4983230072969 + 3 ^ 40 * 3098831 * 2
def baseEnd_3098831 : Nat := 1060793180035247028774161

theorem tailTrace_3098831 : CollatzResearch.WordTrace tailWord_3098831 prefixEnd_3098831 1060793180035247028774161 := by
  unfold tailWord_3098831
  simp only [CollatzResearch.WordTrace]
  refine ⟨113023651836472000045104347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75349101224314666696736231 113023651836472000045104347)
  ·
    refine ⟨169535477754708000067656521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113023651836472000045104347 169535477754708000067656521)
    ·
      refine ⟨127151608316031000050742391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169535477754708000067656521 127151608316031000050742391)
      ·
        refine ⟨190727412474046500076113587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127151608316031000050742391 190727412474046500076113587)
        ·
          refine ⟨286091118711069750114170381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190727412474046500076113587 286091118711069750114170381)
          ·
            refine ⟨107284169516651156292813893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286091118711069750114170381 107284169516651156292813893)
            ·
              refine ⟨20115781784372091804902605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107284169516651156292813893 20115781784372091804902605)
              ·
                refine ⟨7543418169139534426838477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20115781784372091804902605 7543418169139534426838477)
                ·
                  refine ⟨2828781813427325410064429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7543418169139534426838477 2828781813427325410064429)
                  ·
                    refine ⟨1060793180035247028774161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828781813427325410064429 1060793180035247028774161)
                    ·
                      rfl

theorem cell22_3098831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_3098831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098831 prefixEnd_3098831 := by exact prefixLift 3098831
  have htrace : WordTrace (prefixWord ++ tailWord_3098831) baseStart_3098831 baseEnd_3098831 := by
    simpa [prefixWord, tailWord_3098831, baseEnd_3098831] using wordTrace_append hprefix tailTrace_3098831
  have hstable : (prefixWord ++ tailWord_3098831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098831).length < 2 ^ (prefixWord ++ tailWord_3098831).sum := by decide
  have hdescent : baseEnd_3098831 < baseStart_3098831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098859 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 7]
def baseStart_3098859 : Nat := 118140960795 + 3098859 * 2 ^ 59
def prefixEnd_3098859 : Nat := 4983230072969 + 3 ^ 40 * 3098859 * 2
def baseEnd_3098859 : Nat := 1060802765007464289074075

theorem tailTrace_3098859 : CollatzResearch.WordTrace tailWord_3098859 prefixEnd_3098859 1060802765007464289074075 := by
  unfold tailWord_3098859
  simp only [CollatzResearch.WordTrace]
  refine ⟨113024673080370560827123631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75349782053580373884749087 113024673080370560827123631)
  ·
    refine ⟨169537009620555841240685447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113024673080370560827123631 169537009620555841240685447)
    ·
      refine ⟨254305514430833761861028171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169537009620555841240685447 254305514430833761861028171)
      ·
        refine ⟨381458271646250642791542257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254305514430833761861028171 381458271646250642791542257)
        ·
          refine ⟨286093703734687982093656693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381458271646250642791542257 286093703734687982093656693)
          ·
            refine ⟨26821284725126998321280315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286093703734687982093656693 26821284725126998321280315)
            ·
              refine ⟨40231927087690497481920473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26821284725126998321280315 40231927087690497481920473)
              ·
                refine ⟨30173945315767873111440355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40231927087690497481920473 30173945315767873111440355)
                ·
                  refine ⟨45260917973651809667160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30173945315767873111440355 45260917973651809667160533)
                  ·
                    refine ⟨1060802765007464289074075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45260917973651809667160533 1060802765007464289074075)
                    ·
                      rfl

theorem cell22_3098859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_3098859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098859 prefixEnd_3098859 := by exact prefixLift 3098859
  have htrace : WordTrace (prefixWord ++ tailWord_3098859) baseStart_3098859 baseEnd_3098859 := by
    simpa [prefixWord, tailWord_3098859, baseEnd_3098859] using wordTrace_append hprefix tailTrace_3098859
  have hstable : (prefixWord ++ tailWord_3098859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098859).length < 2 ^ (prefixWord ++ tailWord_3098859).sum := by decide
  have hdescent : baseEnd_3098859 < baseStart_3098859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098876 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3098876 : Nat := 118140960795 + 3098876 * 2 ^ 59
def prefixEnd_3098876 : Nat := 4983230072969 + 3 ^ 40 * 3098876 * 2
def baseEnd_3098876 : Nat := 1060808584454881911399023

theorem tailTrace_3098876 : CollatzResearch.WordTrace tailWord_3098876 prefixEnd_3098876 1060808584454881911399023 := by
  unfold tailWord_3098876
  simp only [CollatzResearch.WordTrace]
  refine ⟨56512646560654486365246241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75350195414205981820328321 56512646560654486365246241)
  ·
    refine ⟨42384484920490864773934681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56512646560654486365246241 42384484920490864773934681)
    ·
      refine ⟨31788363690368148580451011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42384484920490864773934681 31788363690368148580451011)
      ·
        refine ⟨47682545535552222870676517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31788363690368148580451011 47682545535552222870676517)
        ·
          refine ⟨8940477287916041788251847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47682545535552222870676517 8940477287916041788251847)
          ·
            refine ⟨13410715931874062682377771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8940477287916041788251847 13410715931874062682377771)
            ·
              refine ⟨20116073897811094023566657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13410715931874062682377771 20116073897811094023566657)
              ·
                refine ⟨15087055423358320517674993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20116073897811094023566657 15087055423358320517674993)
                ·
                  refine ⟨11315291567518740388256245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15087055423358320517674993 11315291567518740388256245)
                  ·
                    refine ⟨1060808584454881911399023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11315291567518740388256245 1060808584454881911399023)
                    ·
                      rfl

theorem cell22_3098876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3098876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098876 prefixEnd_3098876 := by exact prefixLift 3098876
  have htrace : WordTrace (prefixWord ++ tailWord_3098876) baseStart_3098876 baseEnd_3098876 := by
    simpa [prefixWord, tailWord_3098876, baseEnd_3098876] using wordTrace_append hprefix tailTrace_3098876
  have hstable : (prefixWord ++ tailWord_3098876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098876).length < 2 ^ (prefixWord ++ tailWord_3098876).sum := by decide
  have hdescent : baseEnd_3098876 < baseStart_3098876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098882 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3098882 : Nat := 118140960795 + 3098882 * 2 ^ 59
def prefixEnd_3098882 : Nat := 4983230072969 + 3 ^ 40 * 3098882 * 2
def baseEnd_3098882 : Nat := 1060810638377499895749005

theorem tailTrace_3098882 : CollatzResearch.WordTrace tailWord_3098882 prefixEnd_3098882 1060810638377499895749005 := by
  unfold tailWord_3098882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256377989821808938802725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75350341306191490503473933 28256377989821808938802725)
  ·
    refine ⟨5298070873091589176025511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28256377989821808938802725 5298070873091589176025511)
    ·
      refine ⟨7947106309637383764038267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5298070873091589176025511 7947106309637383764038267)
      ·
        refine ⟨11920659464456075646057401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947106309637383764038267 11920659464456075646057401)
        ·
          refine ⟨8940494598342056734543051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11920659464456075646057401 8940494598342056734543051)
          ·
            refine ⟨13410741897513085101814577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8940494598342056734543051 13410741897513085101814577)
            ·
              refine ⟨10058056423134813826360933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13410741897513085101814577 10058056423134813826360933)
              ·
                refine ⟨1885885579337777592442675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10058056423134813826360933 1885885579337777592442675)
                ·
                  refine ⟨2828828369006666388664013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885885579337777592442675 2828828369006666388664013)
                  ·
                    refine ⟨1060810638377499895749005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828828369006666388664013 1060810638377499895749005)
                    ·
                      rfl

theorem cell22_3098882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3098882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098882 prefixEnd_3098882 := by exact prefixLift 3098882
  have htrace : WordTrace (prefixWord ++ tailWord_3098882) baseStart_3098882 baseEnd_3098882 := by
    simpa [prefixWord, tailWord_3098882, baseEnd_3098882] using wordTrace_append hprefix tailTrace_3098882
  have hstable : (prefixWord ++ tailWord_3098882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098882).length < 2 ^ (prefixWord ++ tailWord_3098882).sum := by decide
  have hdescent : baseEnd_3098882 < baseStart_3098882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098936 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3098936 : Nat := 118140960795 + 3098936 * 2 ^ 59
def prefixEnd_3098936 : Nat := 4983230072969 + 3 ^ 40 * 3098936 * 2
def baseEnd_3098936 : Nat := 1060829123681061754898839

theorem tailTrace_3098936 : CollatzResearch.WordTrace tailWord_3098936 prefixEnd_3098936 1060829123681061754898839 := by
  unfold tailWord_3098936
  simp only [CollatzResearch.WordTrace]
  refine ⟨56513740750545801488838331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75351654334061068651784441 56513740750545801488838331)
  ·
    refine ⟨84770611125818702233257497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56513740750545801488838331 84770611125818702233257497)
    ·
      refine ⟨63577958344364026674943123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84770611125818702233257497 63577958344364026674943123)
      ·
        refine ⟨95366937516546040012414685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63577958344364026674943123 95366937516546040012414685)
        ·
          refine ⟨35762601568704765004655507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95366937516546040012414685 35762601568704765004655507)
          ·
            refine ⟨53643902353057147506983261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35762601568704765004655507 53643902353057147506983261)
            ·
              refine ⟨20116463382396430315118723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53643902353057147506983261 20116463382396430315118723)
              ·
                refine ⟨30174695073594645472678085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20116463382396430315118723 30174695073594645472678085)
                ·
                  refine ⟨5657755326298996026127141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30174695073594645472678085 5657755326298996026127141)
                  ·
                    refine ⟨1060829123681061754898839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5657755326298996026127141 1060829123681061754898839)
                    ·
                      rfl

theorem cell22_3098936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3098936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098936 prefixEnd_3098936 := by exact prefixLift 3098936
  have htrace : WordTrace (prefixWord ++ tailWord_3098936) baseStart_3098936 baseEnd_3098936 := by
    simpa [prefixWord, tailWord_3098936, baseEnd_3098936] using wordTrace_append hprefix tailTrace_3098936
  have hstable : (prefixWord ++ tailWord_3098936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098936).length < 2 ^ (prefixWord ++ tailWord_3098936).sum := by decide
  have hdescent : baseEnd_3098936 < baseStart_3098936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098938 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_3098938 : Nat := 118140960795 + 3098938 * 2 ^ 59
def prefixEnd_3098938 : Nat := 4983230072969 + 3 ^ 40 * 3098938 * 2
def baseEnd_3098938 : Nat := 1060829808321934416348833

theorem tailTrace_3098938 : CollatzResearch.WordTrace tailWord_3098938 prefixEnd_3098938 1060829808321934416348833 := by
  unfold tailWord_3098938
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256888611771089329812367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75351702964722904879499645 28256888611771089329812367)
  ·
    refine ⟨42385332917656633994718551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28256888611771089329812367 42385332917656633994718551)
    ·
      refine ⟨63577999376484950992077827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42385332917656633994718551 63577999376484950992077827)
      ·
        refine ⟨95366999064727426488116741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63577999376484950992077827 95366999064727426488116741)
        ·
          refine ⟨17881312324636392466521889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95366999064727426488116741 17881312324636392466521889)
          ·
            refine ⟨13410984243477294349891417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17881312324636392466521889 13410984243477294349891417)
            ·
              refine ⟨10058238182607970762418563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13410984243477294349891417 10058238182607970762418563)
              ·
                refine ⟨15087357273911956143627845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10058238182607970762418563 15087357273911956143627845)
                ·
                  refine ⟨2828879488858491776930221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15087357273911956143627845 2828879488858491776930221)
                  ·
                    refine ⟨1060829808321934416348833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828879488858491776930221 1060829808321934416348833)
                    ·
                      rfl

theorem cell22_3098938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_3098938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098938 prefixEnd_3098938 := by exact prefixLift 3098938
  have htrace : WordTrace (prefixWord ++ tailWord_3098938) baseStart_3098938 baseEnd_3098938 := by
    simpa [prefixWord, tailWord_3098938, baseEnd_3098938] using wordTrace_append hprefix tailTrace_3098938
  have hstable : (prefixWord ++ tailWord_3098938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098938).length < 2 ^ (prefixWord ++ tailWord_3098938).sum := by decide
  have hdescent : baseEnd_3098938 < baseStart_3098938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098940 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_3098940 : Nat := 118140960795 + 3098940 * 2 ^ 59
def prefixEnd_3098940 : Nat := 4983230072969 + 3 ^ 40 * 3098940 * 2
def baseEnd_3098940 : Nat := 353610164320935692599609

theorem tailTrace_3098940 : CollatzResearch.WordTrace tailWord_3098940 prefixEnd_3098940 353610164320935692599609 := by
  unfold tailWord_3098940
  simp only [CollatzResearch.WordTrace]
  refine ⟨56513813696538555830411137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75351751595384741107214849 56513813696538555830411137)
  ·
    refine ⟨42385360272403916872808353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56513813696538555830411137 42385360272403916872808353)
    ·
      refine ⟨31789020204302937654606265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42385360272403916872808353 31789020204302937654606265)
      ·
        refine ⟨23841765153227203240954699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31789020204302937654606265 23841765153227203240954699)
        ·
          refine ⟨35762647729840804861432049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23841765153227203240954699 35762647729840804861432049)
          ·
            refine ⟨26821985797380603646074037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35762647729840804861432049 26821985797380603646074037)
            ·
              refine ⟨2514561168504431591819441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26821985797380603646074037 2514561168504431591819441)
              ·
                refine ⟨1885920876378323693864581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514561168504431591819441 1885920876378323693864581)
                ·
                  refine ⟨353610164320935692599609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1885920876378323693864581 353610164320935692599609)
                  ·
                    rfl

theorem cell22_3098940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_3098940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098940 prefixEnd_3098940 := by exact prefixLift 3098940
  have htrace : WordTrace (prefixWord ++ tailWord_3098940) baseStart_3098940 baseEnd_3098940 := by
    simpa [prefixWord, tailWord_3098940, baseEnd_3098940] using wordTrace_append hprefix tailTrace_3098940
  have hstable : (prefixWord ++ tailWord_3098940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098940).length < 2 ^ (prefixWord ++ tailWord_3098940).sum := by decide
  have hdescent : baseEnd_3098940 < baseStart_3098940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3098951 : List Nat := [1, 1, 4, 1, 2, 2, 4, 7]
def baseStart_3098951 : Nat := 118140960795 + 3098951 * 2 ^ 59
def prefixEnd_3098951 : Nat := 4983230072969 + 3 ^ 40 * 3098951 * 2
def baseEnd_3098951 : Nat := 117870473165289635085977

theorem tailTrace_3098951 : CollatzResearch.WordTrace tailWord_3098951 prefixEnd_3098951 117870473165289635085977 := by
  unfold tailWord_3098951
  simp only [CollatzResearch.WordTrace]
  refine ⟨113028028596037260539472707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75352019064024840359648471 113028028596037260539472707)
  ·
    refine ⟨169542042894055890809209061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113028028596037260539472707 169542042894055890809209061)
    ·
      refine ⟨31789133042635479526726699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169542042894055890809209061 31789133042635479526726699)
      ·
        refine ⟨47683699563953219290090049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31789133042635479526726699 47683699563953219290090049)
        ·
          refine ⟨35762774672964914467567537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47683699563953219290090049 35762774672964914467567537)
          ·
            refine ⟨26822081004723685850675653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35762774672964914467567537 26822081004723685850675653)
            ·
              refine ⟨5029140188385691097001685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26822081004723685850675653 5029140188385691097001685)
              ·
                refine ⟨117870473165289635085977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5029140188385691097001685 117870473165289635085977)
                ·
                  rfl

theorem cell22_3098951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 7].length) (baseStart_3098951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3098951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3098951 prefixEnd_3098951 := by exact prefixLift 3098951
  have htrace : WordTrace (prefixWord ++ tailWord_3098951) baseStart_3098951 baseEnd_3098951 := by
    simpa [prefixWord, tailWord_3098951, baseEnd_3098951] using wordTrace_append hprefix tailTrace_3098951
  have hstable : (prefixWord ++ tailWord_3098951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3098951).length < 2 ^ (prefixWord ++ tailWord_3098951).sum := by decide
  have hdescent : baseEnd_3098951 < baseStart_3098951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3098951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099058 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3099058 : Nat := 118140960795 + 3099058 * 2 ^ 59
def prefixEnd_3099058 : Nat := 4983230072969 + 3 ^ 40 * 3099058 * 2
def baseEnd_3099058 : Nat := 353623628924764701116155

theorem tailTrace_3099058 : CollatzResearch.WordTrace tailWord_3099058 prefixEnd_3099058 353623628924764701116155 := by
  unfold tailWord_3099058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257982801662404453404457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75354620804433078542411885 28257982801662404453404457)
  ·
    refine ⟨21193487101246803340053343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28257982801662404453404457 21193487101246803340053343)
    ·
      refine ⟨31790230651870205010080015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21193487101246803340053343 31790230651870205010080015)
      ·
        refine ⟨47685345977805307515120023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31790230651870205010080015 47685345977805307515120023)
        ·
          refine ⟨71528018966707961272680035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47685345977805307515120023 71528018966707961272680035)
          ·
            refine ⟨107292028450061941909020053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71528018966707961272680035 107292028450061941909020053)
            ·
              refine ⟨5029313833596653526985315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107292028450061941909020053 5029313833596653526985315)
              ·
                refine ⟨7543970750394980290477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029313833596653526985315 7543970750394980290477973)
                ·
                  refine ⟨353623628924764701116155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7543970750394980290477973 353623628924764701116155)
                  ·
                    rfl

theorem cell22_3099058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3099058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099058 prefixEnd_3099058 := by exact prefixLift 3099058
  have htrace : WordTrace (prefixWord ++ tailWord_3099058) baseStart_3099058 baseEnd_3099058 := by
    simpa [prefixWord, tailWord_3099058, baseEnd_3099058] using wordTrace_append hprefix tailTrace_3099058
  have hstable : (prefixWord ++ tailWord_3099058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099058).length < 2 ^ (prefixWord ++ tailWord_3099058).sum := by decide
  have hdescent : baseEnd_3099058 < baseStart_3099058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099092 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_3099092 : Nat := 118140960795 + 3099092 * 2 ^ 59
def prefixEnd_3099092 : Nat := 4983230072969 + 3 ^ 40 * 3099092 * 2
def baseEnd_3099092 : Nat := 353627508556376449332787

theorem tailTrace_3099092 : CollatzResearch.WordTrace tailWord_3099092 prefixEnd_3099092 353627508556376449332787 := by
  unfold tailWord_3099092
  simp only [CollatzResearch.WordTrace]
  refine ⟨56516585644263220810177765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75355447525684294413570353 56516585644263220810177765)
  ·
    refine ⟨10596859808299353901908331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56516585644263220810177765 10596859808299353901908331)
    ·
      refine ⟨15895289712449030852862497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10596859808299353901908331 15895289712449030852862497)
      ·
        refine ⟨11921467284336773139646873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15895289712449030852862497 11921467284336773139646873)
        ·
          refine ⟨8941100463252579854735155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11921467284336773139646873 8941100463252579854735155)
          ·
            refine ⟨13411650694878869782102733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941100463252579854735155 13411650694878869782102733)
            ·
              refine ⟨5029369010579576168288525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13411650694878869782102733 5029369010579576168288525)
              ·
                refine ⟨1886013378967341063108197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5029369010579576168288525 1886013378967341063108197)
                ·
                  refine ⟨353627508556376449332787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886013378967341063108197 353627508556376449332787)
                  ·
                    rfl

theorem cell22_3099092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_3099092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099092 prefixEnd_3099092 := by exact prefixLift 3099092
  have htrace : WordTrace (prefixWord ++ tailWord_3099092) baseStart_3099092 baseEnd_3099092 := by
    simpa [prefixWord, tailWord_3099092, baseEnd_3099092] using wordTrace_append hprefix tailTrace_3099092
  have hstable : (prefixWord ++ tailWord_3099092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099092).length < 2 ^ (prefixWord ++ tailWord_3099092).sum := by decide
  have hdescent : baseEnd_3099092 < baseStart_3099092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099103 : List Nat := [1, 1, 2, 3, 3, 4, 8]
def baseStart_3099103 : Nat := 118140960795 + 3099103 * 2 ^ 59
def prefixEnd_3099103 : Nat := 4983230072969 + 3 ^ 40 * 3099103 * 2
def baseEnd_3099103 : Nat := 39292084859034406887901

theorem tailTrace_3099103 : CollatzResearch.WordTrace tailWord_3099103 prefixEnd_3099103 39292084859034406887901 := by
  unfold tailWord_3099103
  simp only [CollatzResearch.WordTrace]
  refine ⟨113033572491486590499005963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75355714994324393666003975 113033572491486590499005963)
  ·
    refine ⟨169550358737229885748508945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113033572491486590499005963 169550358737229885748508945)
    ·
      refine ⟨127162769052922414311381709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169550358737229885748508945 127162769052922414311381709)
      ·
        refine ⟨47686038394845905366768141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127162769052922414311381709 47686038394845905366768141)
        ·
          refine ⟨17882264398067214512538053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47686038394845905366768141 17882264398067214512538053)
          ·
            refine ⟨3352924574637602721100885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17882264398067214512538053 3352924574637602721100885)
            ·
              refine ⟨39292084859034406887901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3352924574637602721100885 39292084859034406887901)
              ·
                rfl

theorem cell22_3099103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 8].length) (baseStart_3099103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099103 prefixEnd_3099103 := by exact prefixLift 3099103
  have htrace : WordTrace (prefixWord ++ tailWord_3099103) baseStart_3099103 baseEnd_3099103 := by
    simpa [prefixWord, tailWord_3099103, baseEnd_3099103] using wordTrace_append hprefix tailTrace_3099103
  have hstable : (prefixWord ++ tailWord_3099103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099103).length < 2 ^ (prefixWord ++ tailWord_3099103).sum := by decide
  have hdescent : baseEnd_3099103 < baseStart_3099103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099109 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 4]
def baseStart_3099109 : Nat := 118140960795 + 3099109 * 2 ^ 59
def prefixEnd_3099109 : Nat := 4983230072969 + 3 ^ 40 * 3099109 * 2
def baseEnd_3099109 : Nat := 353629448372182323441103

theorem tailTrace_3099109 : CollatzResearch.WordTrace tailWord_3099109 prefixEnd_3099109 353629448372182323441103 := by
  unfold tailWord_3099109
  simp only [CollatzResearch.WordTrace]
  refine ⟨113033791329464853523724381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75355860886309902349149587 113033791329464853523724381)
  ·
    refine ⟨42387671748549320071396643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113033791329464853523724381 42387671748549320071396643)
    ·
      refine ⟨63581507622823980107094965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42387671748549320071396643 63581507622823980107094965)
      ·
        refine ⟨5960766339639748135040153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63581507622823980107094965 5960766339639748135040153)
        ·
          refine ⟨4470574754729811101280115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960766339639748135040153 4470574754729811101280115)
          ·
            refine ⟨6705862132094716651920173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470574754729811101280115 6705862132094716651920173)
            ·
              refine ⟨2514698299535518744470065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6705862132094716651920173 2514698299535518744470065)
              ·
                refine ⟨1886023724651639058352549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514698299535518744470065 1886023724651639058352549)
                ·
                  refine ⟨353629448372182323441103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886023724651639058352549 353629448372182323441103)
                  ·
                    rfl

theorem cell22_3099109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_3099109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099109 prefixEnd_3099109 := by exact prefixLift 3099109
  have htrace : WordTrace (prefixWord ++ tailWord_3099109) baseStart_3099109 baseEnd_3099109 := by
    simpa [prefixWord, tailWord_3099109, baseEnd_3099109] using wordTrace_append hprefix tailTrace_3099109
  have hstable : (prefixWord ++ tailWord_3099109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099109).length < 2 ^ (prefixWord ++ tailWord_3099109).sum := by decide
  have hdescent : baseEnd_3099109 < baseStart_3099109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099165 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3099165 : Nat := 118140960795 + 3099165 * 2 ^ 59
def prefixEnd_3099165 : Nat := 4983230072969 + 3 ^ 40 * 3099165 * 2
def baseEnd_3099165 : Nat := 353635838353660496974379

theorem tailTrace_3099165 : CollatzResearch.WordTrace tailWord_3099165 prefixEnd_3099165 353635838353660496974379 := by
  unfold tailWord_3099165
  simp only [CollatzResearch.WordTrace]
  refine ⟨113035833817261975087762949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75357222544841316725175299 113035833817261975087762949)
  ·
    refine ⟨21194218840736620328955553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113035833817261975087762949 21194218840736620328955553)
    ·
      refine ⟨15895664130552465246716665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21194218840736620328955553 15895664130552465246716665)
      ·
        refine ⟨11921748097914348935037499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15895664130552465246716665 11921748097914348935037499)
        ·
          refine ⟨17882622146871523402556249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11921748097914348935037499 17882622146871523402556249)
          ·
            refine ⟨13411966610153642551917187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17882622146871523402556249 13411966610153642551917187)
            ·
              refine ⟨20117949915230463827875781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13411966610153642551917187 20117949915230463827875781)
              ·
                refine ⟨3772115609105711967726709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20117949915230463827875781 3772115609105711967726709)
                ·
                  refine ⟨353635838353660496974379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772115609105711967726709 353635838353660496974379)
                  ·
                    rfl

theorem cell22_3099165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3099165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099165 prefixEnd_3099165 := by exact prefixLift 3099165
  have htrace : WordTrace (prefixWord ++ tailWord_3099165) baseStart_3099165 baseEnd_3099165 := by
    simpa [prefixWord, tailWord_3099165, baseEnd_3099165] using wordTrace_append hprefix tailTrace_3099165
  have hstable : (prefixWord ++ tailWord_3099165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099165).length < 2 ^ (prefixWord ++ tailWord_3099165).sum := by decide
  have hdescent : baseEnd_3099165 < baseStart_3099165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099255 : List Nat := [1, 1, 3, 1, 1, 3, 6, 6]
def baseStart_3099255 : Nat := 118140960795 + 3099255 * 2 ^ 59
def prefixEnd_3099255 : Nat := 4983230072969 + 3 ^ 40 * 3099255 * 2
def baseEnd_3099255 : Nat := 117882035988916806241429

theorem tailTrace_3099255 : CollatzResearch.WordTrace tailWord_3099255 prefixEnd_3099255 117882035988916806241429 := by
  unfold tailWord_3099255
  simp only [CollatzResearch.WordTrace]
  refine ⟨113039116386935920458539219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75359410924623946972359479 113039116386935920458539219)
  ·
    refine ⟨169558674580403880687808829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113039116386935920458539219 169558674580403880687808829)
    ·
      refine ⟨63584502967651455257928311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169558674580403880687808829 63584502967651455257928311)
      ·
        refine ⟨95376754451477182886892467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63584502967651455257928311 95376754451477182886892467)
        ·
          refine ⟨143065131677215774330338701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95376754451477182886892467 143065131677215774330338701)
          ·
            refine ⟨53649424378955915373877013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143065131677215774330338701 53649424378955915373877013)
            ·
              refine ⟨2514816767763558533150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53649424378955915373877013 2514816767763558533150485)
              ·
                refine ⟨117882035988916806241429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2514816767763558533150485 117882035988916806241429)
                ·
                  rfl

theorem cell22_3099255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 6].length) (baseStart_3099255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099255 prefixEnd_3099255 := by exact prefixLift 3099255
  have htrace : WordTrace (prefixWord ++ tailWord_3099255) baseStart_3099255 baseEnd_3099255 := by
    simpa [prefixWord, tailWord_3099255, baseEnd_3099255] using wordTrace_append hprefix tailTrace_3099255
  have hstable : (prefixWord ++ tailWord_3099255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099255).length < 2 ^ (prefixWord ++ tailWord_3099255).sum := by decide
  have hdescent : baseEnd_3099255 < baseStart_3099255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099261 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 4]
def baseStart_3099261 : Nat := 118140960795 + 3099261 * 2 ^ 59
def prefixEnd_3099261 : Nat := 4983230072969 + 3 ^ 40 * 3099261 * 2
def baseEnd_3099261 : Nat := 353646792607623080174281

theorem tailTrace_3099261 : CollatzResearch.WordTrace tailWord_3099261 prefixEnd_3099261 353646792607623080174281 := by
  unfold tailWord_3099261
  simp only [CollatzResearch.WordTrace]
  refine ⟨113039335224914183483257637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75359556816609455655505091 113039335224914183483257637)
  ·
    refine ⟨21194875354671409403110807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113039335224914183483257637 21194875354671409403110807)
    ·
      refine ⟨31792313032007114104666211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21194875354671409403110807 31792313032007114104666211)
      ·
        refine ⟨47688469548010671156999317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31792313032007114104666211 47688469548010671156999317)
        ·
          refine ⟨2235397010063000210484343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47688469548010671156999317 2235397010063000210484343)
          ·
            refine ⟨3353095515094500315726515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235397010063000210484343 3353095515094500315726515)
            ·
              refine ⟨5029643272641750473589773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353095515094500315726515 5029643272641750473589773)
              ·
                refine ⟨1886116227240656427596165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5029643272641750473589773 1886116227240656427596165)
                ·
                  refine ⟨353646792607623080174281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886116227240656427596165 353646792607623080174281)
                  ·
                    rfl

theorem cell22_3099261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_3099261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099261 prefixEnd_3099261 := by exact prefixLift 3099261
  have htrace : WordTrace (prefixWord ++ tailWord_3099261) baseStart_3099261 baseEnd_3099261 := by
    simpa [prefixWord, tailWord_3099261, baseEnd_3099261] using wordTrace_append hprefix tailTrace_3099261
  have hstable : (prefixWord ++ tailWord_3099261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099261).length < 2 ^ (prefixWord ++ tailWord_3099261).sum := by decide
  have hdescent : baseEnd_3099261 < baseStart_3099261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099338 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3099338 : Nat := 118140960795 + 3099338 * 2 ^ 59
def prefixEnd_3099338 : Nat := 4983230072969 + 3 ^ 40 * 3099338 * 2
def baseEnd_3099338 : Nat := 1060966736496466706347607

theorem tailTrace_3099338 : CollatzResearch.WordTrace tailWord_3099338 prefixEnd_3099338 1060966736496466706347607 := by
  unfold tailWord_3099338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260535911408806408452667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75361429097090150422540445 28260535911408806408452667)
  ·
    refine ⟨42390803867113209612679001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28260535911408806408452667 42390803867113209612679001)
    ·
      refine ⟨31793102900334907209509251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42390803867113209612679001 31793102900334907209509251)
      ·
        refine ⟨47689654350502360814263877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31793102900334907209509251 47689654350502360814263877)
        ·
          refine ⟨8941810190719192652674477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47689654350502360814263877 8941810190719192652674477)
          ·
            refine ⟨3353178821519697244752929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8941810190719192652674477 3353178821519697244752929)
            ·
              refine ⟨2514884116139772933564697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353178821519697244752929 2514884116139772933564697)
              ·
                refine ⟨1886163087104829700173523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514884116139772933564697 1886163087104829700173523)
                ·
                  refine ⟨2829244630657244550260285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886163087104829700173523 2829244630657244550260285)
                  ·
                    refine ⟨1060966736496466706347607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829244630657244550260285 1060966736496466706347607)
                    ·
                      rfl

theorem cell22_3099338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3099338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099338 prefixEnd_3099338 := by exact prefixLift 3099338
  have htrace : WordTrace (prefixWord ++ tailWord_3099338) baseStart_3099338 baseEnd_3099338 := by
    simpa [prefixWord, tailWord_3099338, baseEnd_3099338] using wordTrace_append hprefix tailTrace_3099338
  have hstable : (prefixWord ++ tailWord_3099338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099338).length < 2 ^ (prefixWord ++ tailWord_3099338).sum := by decide
  have hdescent : baseEnd_3099338 < baseStart_3099338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099345 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 6]
def baseStart_3099345 : Nat := 118140960795 + 3099345 * 2 ^ 59
def prefixEnd_3099345 : Nat := 4983230072969 + 3 ^ 40 * 3099345 * 2
def baseEnd_3099345 : Nat := 353656377579840340474195

theorem tailTrace_3099345 : CollatzResearch.WordTrace tailWord_3099345 prefixEnd_3099345 353656377579840340474195 := by
  unfold tailWord_3099345
  simp only [CollatzResearch.WordTrace]
  refine ⟨113042398956609865829315489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75361599304406577219543659 113042398956609865829315489)
  ·
    refine ⟨84781799217457399371986617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113042398956609865829315489 84781799217457399371986617)
    ·
      refine ⟨63586349413093049528989963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84781799217457399371986617 63586349413093049528989963)
      ·
        refine ⟨95379524119639574293484945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63586349413093049528989963 95379524119639574293484945)
        ·
          refine ⟨71534643089729680720113709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95379524119639574293484945 71534643089729680720113709)
          ·
            refine ⟨26825491158648630270042641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71534643089729680720113709 26825491158648630270042641)
            ·
              refine ⟨20119118368986472702531981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26825491158648630270042641 20119118368986472702531981)
              ·
                refine ⟨7544669388369927263449493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20119118368986472702531981 7544669388369927263449493)
                ·
                  refine ⟨353656377579840340474195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7544669388369927263449493 353656377579840340474195)
                  ·
                    rfl

theorem cell22_3099345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_3099345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099345 prefixEnd_3099345 := by exact prefixLift 3099345
  have htrace : WordTrace (prefixWord ++ tailWord_3099345) baseStart_3099345 baseEnd_3099345 := by
    simpa [prefixWord, tailWord_3099345, baseEnd_3099345] using wordTrace_append hprefix tailTrace_3099345
  have hstable : (prefixWord ++ tailWord_3099345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099345).length < 2 ^ (prefixWord ++ tailWord_3099345).sum := by decide
  have hdescent : baseEnd_3099345 < baseStart_3099345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099349 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_3099349 : Nat := 118140960795 + 3099349 * 2 ^ 59
def prefixEnd_3099349 : Nat := 4983230072969 + 3 ^ 40 * 3099349 * 2
def baseEnd_3099349 : Nat := 1060970502021266344322573

theorem tailTrace_3099349 : CollatzResearch.WordTrace tailWord_3099349 prefixEnd_3099349 1060970502021266344322573 := by
  unfold tailWord_3099349
  simp only [CollatzResearch.WordTrace]
  refine ⟨113042544848595374512461101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75361696565730249674974067 113042544848595374512461101)
  ·
    refine ⟨42390954318223265442172913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113042544848595374512461101 42390954318223265442172913)
    ·
      refine ⟨31793215738667449081629685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42390954318223265442172913 31793215738667449081629685)
      ·
        refine ⟨2980613975500073351402783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31793215738667449081629685 2980613975500073351402783)
        ·
          refine ⟨4470920963250110027104175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980613975500073351402783 4470920963250110027104175)
          ·
            refine ⟨6706381444875165040656263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470920963250110027104175 6706381444875165040656263)
            ·
              refine ⟨10059572167312747560984395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706381444875165040656263 10059572167312747560984395)
              ·
                refine ⟨15089358250969121341476593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10059572167312747560984395 15089358250969121341476593)
                ·
                  refine ⟨11317018688226841006107445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15089358250969121341476593 11317018688226841006107445)
                  ·
                    refine ⟨1060970502021266344322573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11317018688226841006107445 1060970502021266344322573)
                    ·
                      rfl

theorem cell22_3099349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_3099349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099349 prefixEnd_3099349 := by exact prefixLift 3099349
  have htrace : WordTrace (prefixWord ++ tailWord_3099349) baseStart_3099349 baseEnd_3099349 := by
    simpa [prefixWord, tailWord_3099349, baseEnd_3099349] using wordTrace_append hprefix tailTrace_3099349
  have hstable : (prefixWord ++ tailWord_3099349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099349).length < 2 ^ (prefixWord ++ tailWord_3099349).sum := by decide
  have hdescent : baseEnd_3099349 < baseStart_3099349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099377 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_3099377 : Nat := 118140960795 + 3099377 * 2 ^ 59
def prefixEnd_3099377 : Nat := 4983230072969 + 3 ^ 40 * 3099377 * 2
def baseEnd_3099377 : Nat := 1060980086993483604622487

theorem tailTrace_3099377 : CollatzResearch.WordTrace tailWord_3099377 prefixEnd_3099377 1060980086993483604622487 := by
  unfold tailWord_3099377
  simp only [CollatzResearch.WordTrace]
  refine ⟨113043566092493935294480385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75362377394995956862986923 113043566092493935294480385)
  ·
    refine ⟨84782674569370451470860289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113043566092493935294480385 84782674569370451470860289)
    ·
      refine ⟨63587005927027838603145217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84782674569370451470860289 63587005927027838603145217)
      ·
        refine ⟨47690254445270878952358913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63587005927027838603145217 47690254445270878952358913)
        ·
          refine ⟨35767690833953159214269185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47690254445270878952358913 35767690833953159214269185)
          ·
            refine ⟨26825768125464869410701889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35767690833953159214269185 26825768125464869410701889)
            ·
              refine ⟨20119326094098652058026417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26825768125464869410701889 20119326094098652058026417)
              ·
                refine ⟨15089494570573989043519813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20119326094098652058026417 15089494570573989043519813)
                ·
                  refine ⟨2829280231982622945659965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15089494570573989043519813 2829280231982622945659965)
                  ·
                    refine ⟨1060980086993483604622487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829280231982622945659965 1060980086993483604622487)
                    ·
                      rfl

theorem cell22_3099377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_3099377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099377 prefixEnd_3099377 := by exact prefixLift 3099377
  have htrace : WordTrace (prefixWord ++ tailWord_3099377) baseStart_3099377 baseEnd_3099377 := by
    simpa [prefixWord, tailWord_3099377, baseEnd_3099377] using wordTrace_append hprefix tailTrace_3099377
  have hstable : (prefixWord ++ tailWord_3099377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099377).length < 2 ^ (prefixWord ++ tailWord_3099377).sum := by decide
  have hdescent : baseEnd_3099377 < baseStart_3099377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099424 : List Nat := [2, 1, 1, 5, 1, 4, 2, 6]
def baseStart_3099424 : Nat := 118140960795 + 3099424 * 2 ^ 59
def prefixEnd_3099424 : Nat := 4983230072969 + 3 ^ 40 * 3099424 * 2
def baseEnd_3099424 : Nat := 117888464005999016521927

theorem tailTrace_3099424 : CollatzResearch.WordTrace tailWord_3099424 prefixEnd_3099424 117888464005999016521927 := by
  unfold tailWord_3099424
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522640161661831160720663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75363520215549108214294217 56522640161661831160720663)
  ·
    refine ⟨84783960242492746741080995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56522640161661831160720663 84783960242492746741080995)
    ·
      refine ⟨127175940363739120111621493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84783960242492746741080995 127175940363739120111621493)
      ·
        refine ⟨11922744409100542510464515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127175940363739120111621493 11922744409100542510464515)
        ·
          refine ⟨17884116613650813765696773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11922744409100542510464515 17884116613650813765696773)
          ·
            refine ⟨3353271865059527581068145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17884116613650813765696773 3353271865059527581068145)
            ·
              refine ⟨2514953898794645685801109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353271865059527581068145 2514953898794645685801109)
              ·
                refine ⟨117888464005999016521927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2514953898794645685801109 117888464005999016521927)
                ·
                  rfl

theorem cell22_3099424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_3099424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099424 prefixEnd_3099424 := by exact prefixLift 3099424
  have htrace : WordTrace (prefixWord ++ tailWord_3099424) baseStart_3099424 baseEnd_3099424 := by
    simpa [prefixWord, tailWord_3099424, baseEnd_3099424] using wordTrace_append hprefix tailTrace_3099424
  have hstable : (prefixWord ++ tailWord_3099424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099424).length < 2 ^ (prefixWord ++ tailWord_3099424).sum := by decide
  have hdescent : baseEnd_3099424 < baseStart_3099424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099435 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 7]
def baseStart_3099435 : Nat := 118140960795 + 3099435 * 2 ^ 59
def prefixEnd_3099435 : Nat := 4983230072969 + 3 ^ 40 * 3099435 * 2
def baseEnd_3099435 : Nat := 353666647192930262224103

theorem tailTrace_3099435 : CollatzResearch.WordTrace tailWord_3099435 prefixEnd_3099435 353666647192930262224103 := by
  unfold tailWord_3099435
  simp only [CollatzResearch.WordTrace]
  refine ⟨113045681526283811200091759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75363787684189207466727839 113045681526283811200091759)
  ·
    refine ⟨169568522289425716800137639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113045681526283811200091759 169568522289425716800137639)
    ·
      refine ⟨254352783434138575200206459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169568522289425716800137639 254352783434138575200206459)
      ·
        refine ⟨381529175151207862800309689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254352783434138575200206459 381529175151207862800309689)
        ·
          refine ⟨286146881363405897100232267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381529175151207862800309689 286146881363405897100232267)
          ·
            refine ⟨429220322045108845650348401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286146881363405897100232267 429220322045108845650348401)
            ·
              refine ⟨321915241533831634237761301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429220322045108845650348401 321915241533831634237761301)
              ·
                refine ⟨15089776946898357854895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 321915241533831634237761301 15089776946898357854895061)
                ·
                  refine ⟨353666647192930262224103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15089776946898357854895061 353666647192930262224103)
                  ·
                    rfl

theorem cell22_3099435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 7].length) (baseStart_3099435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099435 prefixEnd_3099435 := by exact prefixLift 3099435
  have htrace : WordTrace (prefixWord ++ tailWord_3099435) baseStart_3099435 baseEnd_3099435 := by
    simpa [prefixWord, tailWord_3099435, baseEnd_3099435] using wordTrace_append hprefix tailTrace_3099435
  have hstable : (prefixWord ++ tailWord_3099435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099435).length < 2 ^ (prefixWord ++ tailWord_3099435).sum := by decide
  have hdescent : baseEnd_3099435 < baseStart_3099435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099452 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_3099452 : Nat := 118140960795 + 3099452 * 2 ^ 59
def prefixEnd_3099452 : Nat := 4983230072969 + 3 ^ 40 * 3099452 * 2
def baseEnd_3099452 : Nat := 353668587008736136332419

theorem tailTrace_3099452 : CollatzResearch.WordTrace tailWord_3099452 prefixEnd_3099452 353668587008736136332419 := by
  unfold tailWord_3099452
  simp only [CollatzResearch.WordTrace]
  refine ⟨56523150783611111551730305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75364201044814815402307073 56523150783611111551730305)
  ·
    refine ⟨42392363087708333663797729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56523150783611111551730305 42392363087708333663797729)
    ·
      refine ⟨31794272315781250247848297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42392363087708333663797729 31794272315781250247848297)
      ·
        refine ⟨23845704236835937685886223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31794272315781250247848297 23845704236835937685886223)
        ·
          refine ⟨35768556355253906528829335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23845704236835937685886223 35768556355253906528829335)
          ·
            refine ⟨53652834532880859793244003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35768556355253906528829335 53652834532880859793244003)
            ·
              refine ⟨80479251799321289689866005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53652834532880859793244003 80479251799321289689866005)
              ·
                refine ⟨3772464928093185454212469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80479251799321289689866005 3772464928093185454212469)
                ·
                  refine ⟨353668587008736136332419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772464928093185454212469 353668587008736136332419)
                  ·
                    rfl

theorem cell22_3099452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_3099452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099452 prefixEnd_3099452 := by exact prefixLift 3099452
  have htrace : WordTrace (prefixWord ++ tailWord_3099452) baseStart_3099452 baseEnd_3099452 := by
    simpa [prefixWord, tailWord_3099452, baseEnd_3099452] using wordTrace_append hprefix tailTrace_3099452
  have hstable : (prefixWord ++ tailWord_3099452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099452).length < 2 ^ (prefixWord ++ tailWord_3099452).sum := by decide
  have hdescent : baseEnd_3099452 < baseStart_3099452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099462 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3099462 : Nat := 118140960795 + 3099462 * 2 ^ 59
def prefixEnd_3099462 : Nat := 4983230072969 + 3 ^ 40 * 3099462 * 2
def baseEnd_3099462 : Nat := 1061009184230571716247227

theorem tailTrace_3099462 : CollatzResearch.WordTrace tailWord_3099462 prefixEnd_3099462 1061009184230571716247227 := by
  unfold tailWord_3099462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532708321787062337853895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75364444198123996540883093 3532708321787062337853895)
  ·
    refine ⟨5299062482680593506780843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532708321787062337853895 5299062482680593506780843)
    ·
      refine ⟨7948593724020890260171265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299062482680593506780843 7948593724020890260171265)
      ·
        refine ⟨5961445293015667695128449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7948593724020890260171265 5961445293015667695128449)
        ·
          refine ⟨4471083969761750771346337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5961445293015667695128449 4471083969761750771346337)
          ·
            refine ⟨3353312977321313078509753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471083969761750771346337 3353312977321313078509753)
            ·
              refine ⟨2514984732990984808882315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353312977321313078509753 2514984732990984808882315)
              ·
                refine ⟨3772477099486477213323473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514984732990984808882315 3772477099486477213323473)
                ·
                  refine ⟨2829357824614857909992605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772477099486477213323473 2829357824614857909992605)
                  ·
                    refine ⟨1061009184230571716247227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829357824614857909992605 1061009184230571716247227)
                    ·
                      rfl

theorem cell22_3099462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3099462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099462 prefixEnd_3099462 := by exact prefixLift 3099462
  have htrace : WordTrace (prefixWord ++ tailWord_3099462) baseStart_3099462 baseEnd_3099462 := by
    simpa [prefixWord, tailWord_3099462, baseEnd_3099462] using wordTrace_append hprefix tailTrace_3099462
  have hstable : (prefixWord ++ tailWord_3099462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099462).length < 2 ^ (prefixWord ++ tailWord_3099462).sum := by decide
  have hdescent : baseEnd_3099462 < baseStart_3099462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099529 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_3099529 : Nat := 118140960795 + 3099529 * 2 ^ 59
def prefixEnd_3099529 : Nat := 4983230072969 + 3 ^ 40 * 3099529 * 2
def baseEnd_3099529 : Nat := 1061032119699805874822021

theorem tailTrace_3099529 : CollatzResearch.WordTrace tailWord_3099529 prefixEnd_3099529 1061032119699805874822021 := by
  unfold tailWord_3099529
  simp only [CollatzResearch.WordTrace]
  refine ⟨113049109987943265254013641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75366073325295510169342427 113049109987943265254013641)
  ·
    refine ⟨84786832490957448940510231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113049109987943265254013641 84786832490957448940510231)
    ·
      refine ⟨127180248736436173410765347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84786832490957448940510231 127180248736436173410765347)
      ·
        refine ⟨190770373104654260116148021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127180248736436173410765347 190770373104654260116148021)
        ·
          refine ⟨17884722478561336885888877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190770373104654260116148021 17884722478561336885888877)
          ·
            refine ⟨6706770929460501332208329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17884722478561336885888877 6706770929460501332208329)
            ·
              refine ⟨5030078197095375999156247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706770929460501332208329 5030078197095375999156247)
              ·
                refine ⟨7545117295643063998734371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030078197095375999156247 7545117295643063998734371)
                ·
                  refine ⟨11317675943464595998101557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545117295643063998734371 11317675943464595998101557)
                  ·
                    refine ⟨1061032119699805874822021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11317675943464595998101557 1061032119699805874822021)
                    ·
                      rfl

theorem cell22_3099529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_3099529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099529 prefixEnd_3099529 := by exact prefixLift 3099529
  have htrace : WordTrace (prefixWord ++ tailWord_3099529) baseStart_3099529 baseEnd_3099529 := by
    simpa [prefixWord, tailWord_3099529, baseEnd_3099529] using wordTrace_append hprefix tailTrace_3099529
  have hstable : (prefixWord ++ tailWord_3099529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099529).length < 2 ^ (prefixWord ++ tailWord_3099529).sum := by decide
  have hdescent : baseEnd_3099529 < baseStart_3099529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099548 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_3099548 : Nat := 118140960795 + 3099548 * 2 ^ 59
def prefixEnd_3099548 : Nat := 4983230072969 + 3 ^ 40 * 3099548 * 2
def baseEnd_3099548 : Nat := 353679541262698719532321

theorem tailTrace_3099548 : CollatzResearch.WordTrace tailWord_3099548 prefixEnd_3099548 353679541262698719532321 := by
  unfold tailWord_3099548
  simp only [CollatzResearch.WordTrace]
  refine ⟨56524901487437215749477649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75366535316582954332636865 56524901487437215749477649)
  ·
    refine ⟨42393676115577911812108237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56524901487437215749477649 42393676115577911812108237)
    ·
      refine ⟨15897628543341716929540589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42393676115577911812108237 15897628543341716929540589)
      ·
        refine ⟨5961610703753143848577721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15897628543341716929540589 5961610703753143848577721)
        ·
          refine ⟨4471208027814857886433291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5961610703753143848577721 4471208027814857886433291)
          ·
            refine ⟨6706812041722286829649937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471208027814857886433291 6706812041722286829649937)
            ·
              refine ⟨5030109031291715122237453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706812041722286829649937 5030109031291715122237453)
              ·
                refine ⟨1886290886734393170839045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5030109031291715122237453 1886290886734393170839045)
                ·
                  refine ⟨353679541262698719532321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886290886734393170839045 353679541262698719532321)
                  ·
                    rfl

theorem cell22_3099548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_3099548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099548 prefixEnd_3099548 := by exact prefixLift 3099548
  have htrace : WordTrace (prefixWord ++ tailWord_3099548) baseStart_3099548 baseEnd_3099548 := by
    simpa [prefixWord, tailWord_3099548, baseEnd_3099548] using wordTrace_append hprefix tailTrace_3099548
  have hstable : (prefixWord ++ tailWord_3099548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099548).length < 2 ^ (prefixWord ++ tailWord_3099548).sum := by decide
  have hdescent : baseEnd_3099548 < baseStart_3099548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099559 : List Nat := [1, 1, 6, 1, 3, 1, 9]
def baseStart_3099559 : Nat := 118140960795 + 3099559 * 2 ^ 59
def prefixEnd_3099559 : Nat := 4983230072969 + 3 ^ 40 * 3099559 * 2
def baseEnd_3099559 : Nat := 39297866270847992465627

theorem tailTrace_3099559 : CollatzResearch.WordTrace tailWord_3099559 prefixEnd_3099559 39297866270847992465627 := by
  unfold tailWord_3099559
  simp only [CollatzResearch.WordTrace]
  refine ⟨113050204177834580377605731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75366802785223053585070487 113050204177834580377605731)
  ·
    refine ⟨169575306266751870566408597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113050204177834580377605731 169575306266751870566408597)
    ·
      refine ⟨7948842481253993932800403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169575306266751870566408597 7948842481253993932800403)
      ·
        refine ⟨11923263721880990899200605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7948842481253993932800403 11923263721880990899200605)
        ·
          refine ⟨4471223895705371587200227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11923263721880990899200605 4471223895705371587200227)
          ·
            refine ⟨6706835843558057380800341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471223895705371587200227 6706835843558057380800341)
            ·
              refine ⟨39297866270847992465627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6706835843558057380800341 39297866270847992465627)
              ·
                rfl

theorem cell22_3099559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 9].length) (baseStart_3099559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099559 prefixEnd_3099559 := by exact prefixLift 3099559
  have htrace : WordTrace (prefixWord ++ tailWord_3099559) baseStart_3099559 baseEnd_3099559 := by
    simpa [prefixWord, tailWord_3099559, baseEnd_3099559] using wordTrace_append hprefix tailTrace_3099559
  have hstable : (prefixWord ++ tailWord_3099559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099559).length < 2 ^ (prefixWord ++ tailWord_3099559).sum := by decide
  have hdescent : baseEnd_3099559 < baseStart_3099559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099604 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3099604 : Nat := 118140960795 + 3099604 * 2 ^ 59
def prefixEnd_3099604 : Nat := 4983230072969 + 3 ^ 40 * 3099604 * 2
def baseEnd_3099604 : Nat := 353685931244176893065597

theorem tailTrace_3099604 : CollatzResearch.WordTrace tailWord_3099604 prefixEnd_3099604 353685931244176893065597 := by
  unfold tailWord_3099604
  simp only [CollatzResearch.WordTrace]
  refine ⟨56525922731335776531496933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75367896975114368708662577 56525922731335776531496933)
  ·
    refine ⟨10598610512125458099655675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56525922731335776531496933 10598610512125458099655675)
    ·
      refine ⟨15897915768188187149483513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598610512125458099655675 15897915768188187149483513)
      ·
        refine ⟨11923436826141140362112635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15897915768188187149483513 11923436826141140362112635)
        ·
          refine ⟨17885155239211710543168953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11923436826141140362112635 17885155239211710543168953)
          ·
            refine ⟨13413866429408782907376715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17885155239211710543168953 13413866429408782907376715)
            ·
              refine ⟨20120799644113174361065073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13413866429408782907376715 20120799644113174361065073)
              ·
                refine ⟨15090599733084880770798805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20120799644113174361065073 15090599733084880770798805)
                ·
                  refine ⟨353685931244176893065597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15090599733084880770798805 353685931244176893065597)
                  ·
                    rfl

theorem cell22_3099604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3099604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099604 prefixEnd_3099604 := by exact prefixLift 3099604
  have htrace : WordTrace (prefixWord ++ tailWord_3099604) baseStart_3099604 baseEnd_3099604 := by
    simpa [prefixWord, tailWord_3099604, baseEnd_3099604] using wordTrace_append hprefix tailTrace_3099604
  have hstable : (prefixWord ++ tailWord_3099604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099604).length < 2 ^ (prefixWord ++ tailWord_3099604).sum := by decide
  have hdescent : baseEnd_3099604 < baseStart_3099604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099608 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 1, 3]
def baseStart_3099608 : Nat := 118140960795 + 3099608 * 2 ^ 59
def prefixEnd_3099608 : Nat := 4983230072969 + 3 ^ 40 * 3099608 * 2
def baseEnd_3099608 : Nat := 1061059163014276002096779

theorem tailTrace_3099608 : CollatzResearch.WordTrace tailWord_3099608 prefixEnd_3099608 1061059163014276002096779 := by
  unfold tailWord_3099608
  simp only [CollatzResearch.WordTrace]
  refine ⟨56525995677328530873069739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75367994236438041164092985 56525995677328530873069739)
  ·
    refine ⟨84788993515992796309604609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56525995677328530873069739 84788993515992796309604609)
    ·
      refine ⟨63591745136994597232203457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84788993515992796309604609 63591745136994597232203457)
      ·
        refine ⟨47693808852745947924152593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63591745136994597232203457 47693808852745947924152593)
        ·
          refine ⟨35770356639559460943114445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47693808852745947924152593 35770356639559460943114445)
          ·
            refine ⟨13413883739834797853667917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35770356639559460943114445 13413883739834797853667917)
            ·
              refine ⟨5030206402438049195125469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13413883739834797853667917 5030206402438049195125469)
              ·
                refine ⟨1886327400914268448172051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5030206402438049195125469 1886327400914268448172051)
                ·
                  refine ⟨2829491101371402672258077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886327400914268448172051 2829491101371402672258077)
                  ·
                    refine ⟨1061059163014276002096779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829491101371402672258077 1061059163014276002096779)
                    ·
                      rfl

theorem cell22_3099608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_3099608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099608 prefixEnd_3099608 := by exact prefixLift 3099608
  have htrace : WordTrace (prefixWord ++ tailWord_3099608) baseStart_3099608 baseEnd_3099608 := by
    simpa [prefixWord, tailWord_3099608, baseEnd_3099608] using wordTrace_append hprefix tailTrace_3099608
  have hstable : (prefixWord ++ tailWord_3099608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099608).length < 2 ^ (prefixWord ++ tailWord_3099608).sum := by decide
  have hdescent : baseEnd_3099608 < baseStart_3099608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099638 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3099638 : Nat := 118140960795 + 3099638 * 2 ^ 59
def prefixEnd_3099638 : Nat := 4983230072969 + 3 ^ 40 * 3099638 * 2
def baseEnd_3099638 : Nat := 353689810875788641282229

theorem tailTrace_3099638 : CollatzResearch.WordTrace tailWord_3099638 prefixEnd_3099638 353689810875788641282229 := by
  unfold tailWord_3099638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065817846534273554358223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75368723696365584579821045 7065817846534273554358223)
  ·
    refine ⟨10598726769801410331537335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7065817846534273554358223 10598726769801410331537335)
    ·
      refine ⟨15898090154702115497306003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598726769801410331537335 15898090154702115497306003)
      ·
        refine ⟨23847135232053173245959005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15898090154702115497306003 23847135232053173245959005)
        ·
          refine ⟨8942675712019939967234627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23847135232053173245959005 8942675712019939967234627)
          ·
            refine ⟨13414013568029909950851941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8942675712019939967234627 13414013568029909950851941)
            ·
              refine ⟨2515127544005608115784739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13414013568029909950851941 2515127544005608115784739)
              ·
                refine ⟨3772691316008412173677109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515127544005608115784739 3772691316008412173677109)
                ·
                  refine ⟨353689810875788641282229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772691316008412173677109 353689810875788641282229)
                  ·
                    rfl

theorem cell22_3099638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3099638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099638 prefixEnd_3099638 := by exact prefixLift 3099638
  have htrace : WordTrace (prefixWord ++ tailWord_3099638) baseStart_3099638 baseEnd_3099638 := by
    simpa [prefixWord, tailWord_3099638, baseEnd_3099638] using wordTrace_append hprefix tailTrace_3099638
  have hstable : (prefixWord ++ tailWord_3099638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099638).length < 2 ^ (prefixWord ++ tailWord_3099638).sum := by decide
  have hdescent : baseEnd_3099638 < baseStart_3099638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099683 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 4]
def baseStart_3099683 : Nat := 118140960795 + 3099683 * 2 ^ 59
def prefixEnd_3099683 : Nat := 4983230072969 + 3 ^ 40 * 3099683 * 2
def baseEnd_3099683 : Nat := 353694945682333602157183

theorem tailTrace_3099683 : CollatzResearch.WordTrace tailWord_3099683 prefixEnd_3099683 353694945682333602157183 := by
  unfold tailWord_3099683
  simp only [CollatzResearch.WordTrace]
  refine ⟨113054726829385349555119703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75369817886256899703413135 113054726829385349555119703)
  ·
    refine ⟨169582090244078024332679555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113054726829385349555119703 169582090244078024332679555)
    ·
      refine ⟨254373135366117036499019333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169582090244078024332679555 254373135366117036499019333)
      ·
        refine ⟨47694962881146944343566125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254373135366117036499019333 47694962881146944343566125)
        ·
          refine ⟨17885611080430104128837297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47694962881146944343566125 17885611080430104128837297)
          ·
            refine ⟨13414208310322578096627973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17885611080430104128837297 13414208310322578096627973)
            ·
              refine ⟨2515164058185483393117745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13414208310322578096627973 2515164058185483393117745)
              ·
                refine ⟨1886373043639112544838309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515164058185483393117745 1886373043639112544838309)
                ·
                  refine ⟨353694945682333602157183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886373043639112544838309 353694945682333602157183)
                  ·
                    rfl

theorem cell22_3099683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 4].length) (baseStart_3099683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099683 prefixEnd_3099683 := by exact prefixLift 3099683
  have htrace : WordTrace (prefixWord ++ tailWord_3099683) baseStart_3099683 baseEnd_3099683 := by
    simpa [prefixWord, tailWord_3099683, baseEnd_3099683] using wordTrace_append hprefix tailTrace_3099683
  have hstable : (prefixWord ++ tailWord_3099683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099683).length < 2 ^ (prefixWord ++ tailWord_3099683).sum := by decide
  have hdescent : baseEnd_3099683 < baseStart_3099683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099726 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_3099726 : Nat := 118140960795 + 3099726 * 2 ^ 59
def prefixEnd_3099726 : Nat := 4983230072969 + 3 ^ 40 * 3099726 * 2
def baseEnd_3099726 : Nat := 1061099556825763027646417

theorem tailTrace_3099726 : CollatzResearch.WordTrace tailWord_3099726 prefixEnd_3099726 1061099556825763027646417 := by
  unfold tailWord_3099726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132036896028695987366879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75370863445486378599290021 14132036896028695987366879)
  ·
    refine ⟨21198055344043043981050319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14132036896028695987366879 21198055344043043981050319)
    ·
      refine ⟨31797083016064565971575479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21198055344043043981050319 31797083016064565971575479)
      ·
        refine ⟨47695624524096848957363219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31797083016064565971575479 47695624524096848957363219)
        ·
          refine ⟨71543436786145273436044829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47695624524096848957363219 71543436786145273436044829)
          ·
            refine ⟨26828788794804477538516811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71543436786145273436044829 26828788794804477538516811)
            ·
              refine ⟨40243183192206716307775217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26828788794804477538516811 40243183192206716307775217)
              ·
                refine ⟨30182387394155037230831413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40243183192206716307775217 30182387394155037230831413)
                ·
                  refine ⟨2829598818202034740390445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30182387394155037230831413 2829598818202034740390445)
                  ·
                    refine ⟨1061099556825763027646417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829598818202034740390445 1061099556825763027646417)
                    ·
                      rfl

theorem cell22_3099726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_3099726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099726 prefixEnd_3099726 := by exact prefixLift 3099726
  have htrace : WordTrace (prefixWord ++ tailWord_3099726) baseStart_3099726 baseEnd_3099726 := by
    simpa [prefixWord, tailWord_3099726, baseEnd_3099726] using wordTrace_append hprefix tailTrace_3099726
  have hstable : (prefixWord ++ tailWord_3099726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099726).length < 2 ^ (prefixWord ++ tailWord_3099726).sum := by decide
  have hdescent : baseEnd_3099726 < baseStart_3099726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099743 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 1, 3]
def baseStart_3099743 : Nat := 118140960795 + 3099743 * 2 ^ 59
def prefixEnd_3099743 : Nat := 4983230072969 + 3 ^ 40 * 3099743 * 2
def baseEnd_3099743 : Nat := 1061105376273180649971365

theorem tailTrace_3099743 : CollatzResearch.WordTrace tailWord_3099743 prefixEnd_3099743 1061105376273180649971365 := by
  unfold tailWord_3099743
  simp only [CollatzResearch.WordTrace]
  refine ⟨113056915209167979802303883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75371276806111986534869255 113056915209167979802303883)
  ·
    refine ⟨169585372813751969703455825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113056915209167979802303883 169585372813751969703455825)
    ·
      refine ⟨127189029610313977277591869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169585372813751969703455825 127189029610313977277591869)
      ·
        refine ⟨47695886103867741479096951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127189029610313977277591869 47695886103867741479096951)
        ·
          refine ⟨71543829155801612218645427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47695886103867741479096951 71543829155801612218645427)
          ·
            refine ⟨107315743733702418327968141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71543829155801612218645427 107315743733702418327968141)
            ·
              refine ⟨40243403900138406872988053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107315743733702418327968141 40243403900138406872988053)
              ·
                refine ⟨1886409557818987822171315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40243403900138406872988053 1886409557818987822171315)
                ·
                  refine ⟨2829614336728481733256973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886409557818987822171315 2829614336728481733256973)
                  ·
                    refine ⟨1061105376273180649971365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829614336728481733256973 1061105376273180649971365)
                    ·
                      rfl

theorem cell22_3099743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_3099743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099743 prefixEnd_3099743 := by exact prefixLift 3099743
  have htrace : WordTrace (prefixWord ++ tailWord_3099743) baseStart_3099743 baseEnd_3099743 := by
    simpa [prefixWord, tailWord_3099743, baseEnd_3099743] using wordTrace_append hprefix tailTrace_3099743
  have hstable : (prefixWord ++ tailWord_3099743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099743).length < 2 ^ (prefixWord ++ tailWord_3099743).sum := by decide
  have hdescent : baseEnd_3099743 < baseStart_3099743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099777 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3099777 : Nat := 118140960795 + 3099777 * 2 ^ 59
def prefixEnd_3099777 : Nat := 4983230072969 + 3 ^ 40 * 3099777 * 2
def baseEnd_3099777 : Nat := 1061117015168015894621261

theorem tailTrace_3099777 : CollatzResearch.WordTrace tailWord_3099777 prefixEnd_3099777 1061117015168015894621261 := by
  unfold tailWord_3099777
  simp only [CollatzResearch.WordTrace]
  refine ⟨113058155291044803609041585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75372103527363202406027723 113058155291044803609041585)
  ·
    refine ⟨84793616468283602706781189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113058155291044803609041585 84793616468283602706781189)
    ·
      refine ⟨15898803087803175507521473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84793616468283602706781189 15898803087803175507521473)
      ·
        refine ⟨11924102315852381630641105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15898803087803175507521473 11924102315852381630641105)
        ·
          refine ⟨8943076736889286222980829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924102315852381630641105 8943076736889286222980829)
          ·
            refine ⟨3353653776333482333617811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8943076736889286222980829 3353653776333482333617811)
            ·
              refine ⟨5030480664500223500426717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353653776333482333617811 5030480664500223500426717)
              ·
                refine ⟨1886430249187583812660019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5030480664500223500426717 1886430249187583812660019)
                ·
                  refine ⟨2829645373781375718990029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886430249187583812660019 2829645373781375718990029)
                  ·
                    refine ⟨1061117015168015894621261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829645373781375718990029 1061117015168015894621261)
                    ·
                      rfl

theorem cell22_3099777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3099777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099777 prefixEnd_3099777 := by exact prefixLift 3099777
  have htrace : WordTrace (prefixWord ++ tailWord_3099777) baseStart_3099777 baseEnd_3099777 := by
    simpa [prefixWord, tailWord_3099777, baseEnd_3099777] using wordTrace_append hprefix tailTrace_3099777
  have hstable : (prefixWord ++ tailWord_3099777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099777).length < 2 ^ (prefixWord ++ tailWord_3099777).sum := by decide
  have hdescent : baseEnd_3099777 < baseStart_3099777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099807 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 5]
def baseStart_3099807 : Nat := 118140960795 + 3099807 * 2 ^ 59
def prefixEnd_3099807 : Nat := 4983230072969 + 3 ^ 40 * 3099807 * 2
def baseEnd_3099807 : Nat := 353709094927035272123723

theorem tailTrace_3099807 : CollatzResearch.WordTrace tailWord_3099807 prefixEnd_3099807 353709094927035272123723 := by
  unfold tailWord_3099807
  simp only [CollatzResearch.WordTrace]
  refine ⟨113059249480936118732633675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75372832987290745821755783 113059249480936118732633675)
  ·
    refine ⟨169588874221404178098950513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113059249480936118732633675 169588874221404178098950513)
    ·
      refine ⟨127191655666053133574212885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169588874221404178098950513 127191655666053133574212885)
      ·
        refine ⟨5962108859346240636291229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127191655666053133574212885 5962108859346240636291229)
        ·
          refine ⟨2235790822254840238609211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5962108859346240636291229 2235790822254840238609211)
          ·
            refine ⟨3353686233382260357913817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235790822254840238609211 3353686233382260357913817)
            ·
              refine ⟨2515264675036695268435363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353686233382260357913817 2515264675036695268435363)
              ·
                refine ⟨3772897012555042902653045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515264675036695268435363 3772897012555042902653045)
                ·
                  refine ⟨353709094927035272123723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3772897012555042902653045 353709094927035272123723)
                  ·
                    rfl

theorem cell22_3099807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 5].length) (baseStart_3099807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099807 prefixEnd_3099807 := by exact prefixLift 3099807
  have htrace : WordTrace (prefixWord ++ tailWord_3099807) baseStart_3099807 baseEnd_3099807 := by
    simpa [prefixWord, tailWord_3099807, baseEnd_3099807] using wordTrace_append hprefix tailTrace_3099807
  have hstable : (prefixWord ++ tailWord_3099807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099807).length < 2 ^ (prefixWord ++ tailWord_3099807).sum := by decide
  have hdescent : baseEnd_3099807 < baseStart_3099807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099850 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_3099850 : Nat := 118140960795 + 3099850 * 2 ^ 59
def prefixEnd_3099850 : Nat := 4983230072969 + 3 ^ 40 * 3099850 * 2
def baseEnd_3099850 : Nat := 1061142004559868037546037

theorem tailTrace_3099850 : CollatzResearch.WordTrace tailWord_3099850 prefixEnd_3099850 1061142004559868037546037 := by
  unfold tailWord_3099850
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265204454945084269112251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75373878546520224717632669 28265204454945084269112251)
  ·
    refine ⟨42397806682417626403668377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28265204454945084269112251 42397806682417626403668377)
    ·
      refine ⟨31798355011813219802751283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42397806682417626403668377 31798355011813219802751283)
      ·
        refine ⟨47697532517719829704126925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31798355011813219802751283 47697532517719829704126925)
        ·
          refine ⟨17886574694144936139047597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47697532517719829704126925 17886574694144936139047597)
          ·
            refine ⟨6707465510304351052142849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17886574694144936139047597 6707465510304351052142849)
            ·
              refine ⟨5030599132728263289107137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707465510304351052142849 5030599132728263289107137)
              ·
                refine ⟨3772949349546197466830353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030599132728263289107137 3772949349546197466830353)
                ·
                  refine ⟨2829712012159648100122765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3772949349546197466830353 2829712012159648100122765)
                  ·
                    refine ⟨1061142004559868037546037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829712012159648100122765 1061142004559868037546037)
                    ·
                      rfl

theorem cell22_3099850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_3099850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099850 prefixEnd_3099850 := by exact prefixLift 3099850
  have htrace : WordTrace (prefixWord ++ tailWord_3099850) baseStart_3099850 baseEnd_3099850 := by
    simpa [prefixWord, tailWord_3099850, baseEnd_3099850] using wordTrace_append hprefix tailTrace_3099850
  have hstable : (prefixWord ++ tailWord_3099850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099850).length < 2 ^ (prefixWord ++ tailWord_3099850).sum := by decide
  have hdescent : baseEnd_3099850 < baseStart_3099850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099908 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_3099908 : Nat := 118140960795 + 3099908 * 2 ^ 59
def prefixEnd_3099908 : Nat := 4983230072969 + 3 ^ 40 * 3099908 * 2
def baseEnd_3099908 : Nat := 353720619715058406531953

theorem tailTrace_3099908 : CollatzResearch.WordTrace tailWord_3099908 prefixEnd_3099908 353720619715058406531953 := by
  unfold tailWord_3099908
  simp only [CollatzResearch.WordTrace]
  refine ⟨56531466626785106491030189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75375288835713475321373585 56531466626785106491030189)
  ·
    refine ⟨21199299985044414934136321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56531466626785106491030189 21199299985044414934136321)
    ·
      refine ⟨15899474988783311200602241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21199299985044414934136321 15899474988783311200602241)
      ·
        refine ⟨11924606241587483400451681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15899474988783311200602241 11924606241587483400451681)
        ·
          refine ⟨8943454681190612550338761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924606241587483400451681 8943454681190612550338761)
          ·
            refine ⟨6707591010892959412754071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8943454681190612550338761 6707591010892959412754071)
            ·
              refine ⟨10061386516339439119131107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6707591010892959412754071 10061386516339439119131107)
              ·
                refine ⟨15092079774509158678696661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10061386516339439119131107 15092079774509158678696661)
                ·
                  refine ⟨353720619715058406531953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15092079774509158678696661 353720619715058406531953)
                  ·
                    rfl

theorem cell22_3099908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_3099908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099908 prefixEnd_3099908 := by exact prefixLift 3099908
  have htrace : WordTrace (prefixWord ++ tailWord_3099908) baseStart_3099908 baseEnd_3099908 := by
    simpa [prefixWord, tailWord_3099908, baseEnd_3099908] using wordTrace_append hprefix tailTrace_3099908
  have hstable : (prefixWord ++ tailWord_3099908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099908).length < 2 ^ (prefixWord ++ tailWord_3099908).sum := by decide
  have hdescent : baseEnd_3099908 < baseStart_3099908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099951 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3099951 : Nat := 118140960795 + 3099951 * 2 ^ 59
def prefixEnd_3099951 : Nat := 4983230072969 + 3 ^ 40 * 3099951 * 2
def baseEnd_3099951 : Nat := 1061176578923937440770727

theorem tailTrace_3099951 : CollatzResearch.WordTrace tailWord_3099951 prefixEnd_3099951 1061176578923937440770727 := by
  unfold tailWord_3099951
  simp only [CollatzResearch.WordTrace]
  refine ⟨113064501592414431325875707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75376334394942954217250471 113064501592414431325875707)
  ·
    refine ⟨169596752388621646988813561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113064501592414431325875707 169596752388621646988813561)
    ·
      refine ⟨127197564291466235241610171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169596752388621646988813561 127197564291466235241610171)
      ·
        refine ⟨190796346437199352862415257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127197564291466235241610171 190796346437199352862415257)
        ·
          refine ⟨143097259827899514646811443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190796346437199352862415257 143097259827899514646811443)
          ·
            refine ⟨214645889741849271970217165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143097259827899514646811443 214645889741849271970217165)
            ·
              refine ⟨80492208653193476988831437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214645889741849271970217165 80492208653193476988831437)
              ·
                refine ⟨30184578244947553870811789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80492208653193476988831437 30184578244947553870811789)
                ·
                  refine ⟨11319216841855332701554421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30184578244947553870811789 11319216841855332701554421)
                  ·
                    refine ⟨1061176578923937440770727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11319216841855332701554421 1061176578923937440770727)
                    ·
                      rfl

theorem cell22_3099951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3099951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099951 prefixEnd_3099951 := by exact prefixLift 3099951
  have htrace : WordTrace (prefixWord ++ tailWord_3099951) baseStart_3099951 baseEnd_3099951 := by
    simpa [prefixWord, tailWord_3099951, baseEnd_3099951] using wordTrace_append hprefix tailTrace_3099951
  have hstable : (prefixWord ++ tailWord_3099951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099951).length < 2 ^ (prefixWord ++ tailWord_3099951).sum := by decide
  have hdescent : baseEnd_3099951 < baseStart_3099951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099968 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_3099968 : Nat := 118140960795 + 3099968 * 2 ^ 59
def prefixEnd_3099968 : Nat := 4983230072969 + 3 ^ 40 * 3099968 * 2
def baseEnd_3099968 : Nat := 1061182398371355063095675

theorem tailTrace_3099968 : CollatzResearch.WordTrace tailWord_3099968 prefixEnd_3099968 1061182398371355063095675 := by
  unfold tailWord_3099968
  simp only [CollatzResearch.WordTrace]
  refine ⟨56532560816676421614622279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75376747755568562152829705 56532560816676421614622279)
  ·
    refine ⟨84798841225014632421933419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56532560816676421614622279 84798841225014632421933419)
    ·
      refine ⟨127198261837521948632900129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84798841225014632421933419 127198261837521948632900129)
      ·
        refine ⟨95398696378141461474675097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127198261837521948632900129 95398696378141461474675097)
        ·
          refine ⟨71549022283606096106006323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95398696378141461474675097 71549022283606096106006323)
          ·
            refine ⟨107323533425409144159009485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71549022283606096106006323 107323533425409144159009485)
            ·
              refine ⟨40246325034528429059628557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107323533425409144159009485 40246325034528429059628557)
              ·
                refine ⟨15092371887948160897360709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40246325034528429059628557 15092371887948160897360709)
                ·
                  refine ⟨2829819728990280168255133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15092371887948160897360709 2829819728990280168255133)
                  ·
                    refine ⟨1061182398371355063095675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829819728990280168255133 1061182398371355063095675)
                    ·
                      rfl

theorem cell22_3099968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_3099968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099968 prefixEnd_3099968 := by exact prefixLift 3099968
  have htrace : WordTrace (prefixWord ++ tailWord_3099968) baseStart_3099968 baseEnd_3099968 := by
    simpa [prefixWord, tailWord_3099968, baseEnd_3099968] using wordTrace_append hprefix tailTrace_3099968
  have hstable : (prefixWord ++ tailWord_3099968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099968).length < 2 ^ (prefixWord ++ tailWord_3099968).sum := by decide
  have hdescent : baseEnd_3099968 < baseStart_3099968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3099985 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_3099985 : Nat := 118140960795 + 3099985 * 2 ^ 59
def prefixEnd_3099985 : Nat := 4983230072969 + 3 ^ 40 * 3099985 * 2
def baseEnd_3099985 : Nat := 1061188217818772685420623

theorem tailTrace_3099985 : CollatzResearch.WordTrace tailWord_3099985 prefixEnd_3099985 1061188217818772685420623 := by
  unfold tailWord_3099985
  simp only [CollatzResearch.WordTrace]
  refine ⟨113065741674291255132613409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75377161116194170088408939 113065741674291255132613409)
  ·
    refine ⟨84799306255718441349460057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113065741674291255132613409 84799306255718441349460057)
    ·
      refine ⟨63599479691788831012095043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84799306255718441349460057 63599479691788831012095043)
      ·
        refine ⟨95399219537683246518142565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63599479691788831012095043 95399219537683246518142565)
        ·
          refine ⟨17887353663315608722151731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95399219537683246518142565 17887353663315608722151731)
          ·
            refine ⟨26831030494973413083227597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887353663315608722151731 26831030494973413083227597)
            ·
              refine ⟨10061636435615029906210349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26831030494973413083227597 10061636435615029906210349)
              ·
                refine ⟨3773113663355636214828881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10061636435615029906210349 3773113663355636214828881)
                ·
                  refine ⟨2829835247516727161121661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773113663355636214828881 2829835247516727161121661)
                  ·
                    refine ⟨1061188217818772685420623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829835247516727161121661 1061188217818772685420623)
                    ·
                      rfl

theorem cell22_3099985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_3099985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3099985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3099985 prefixEnd_3099985 := by exact prefixLift 3099985
  have htrace : WordTrace (prefixWord ++ tailWord_3099985) baseStart_3099985 baseEnd_3099985 := by
    simpa [prefixWord, tailWord_3099985, baseEnd_3099985] using wordTrace_append hprefix tailTrace_3099985
  have hstable : (prefixWord ++ tailWord_3099985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3099985).length < 2 ^ (prefixWord ++ tailWord_3099985).sum := by decide
  have hdescent : baseEnd_3099985 < baseStart_3099985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3099985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100000 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_3100000 : Nat := 118140960795 + 3100000 * 2 ^ 59
def prefixEnd_3100000 : Nat := 4983230072969 + 3 ^ 40 * 3100000 * 2
def baseEnd_3100000 : Nat := 1061193352625317646295577

theorem tailTrace_3100000 : CollatzResearch.WordTrace tailWord_3100000 prefixEnd_3100000 1061193352625317646295577 := by
  unfold tailWord_3100000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56533144384618456347204727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75377525846157941796272969 56533144384618456347204727)
  ·
    refine ⟨84799716576927684520807091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56533144384618456347204727 84799716576927684520807091)
    ·
      refine ⟨127199574865391526781210637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84799716576927684520807091 127199574865391526781210637)
      ·
        refine ⟨47699840574521822542953989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127199574865391526781210637 47699840574521822542953989)
        ·
          refine ⟨8943720107722841726803873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47699840574521822542953989 8943720107722841726803873)
          ·
            refine ⟨6707790080792131295102905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8943720107722841726803873 6707790080792131295102905)
            ·
              refine ⟨5030842560594098471327179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707790080792131295102905 5030842560594098471327179)
              ·
                refine ⟨7546263840891147706990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030842560594098471327179 7546263840891147706990769)
                ·
                  refine ⟨5659697880668360780243077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7546263840891147706990769 5659697880668360780243077)
                  ·
                    refine ⟨1061193352625317646295577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659697880668360780243077 1061193352625317646295577)
                    ·
                      rfl

theorem cell22_3100000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_3100000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100000 prefixEnd_3100000 := by exact prefixLift 3100000
  have htrace : WordTrace (prefixWord ++ tailWord_3100000) baseStart_3100000 baseEnd_3100000 := by
    simpa [prefixWord, tailWord_3100000, baseEnd_3100000] using wordTrace_append hprefix tailTrace_3100000
  have hstable : (prefixWord ++ tailWord_3100000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100000).length < 2 ^ (prefixWord ++ tailWord_3100000).sum := by decide
  have hdescent : baseEnd_3100000 < baseStart_3100000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100011 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 8]
def baseStart_3100011 : Nat := 118140960795 + 3100011 * 2 ^ 59
def prefixEnd_3100011 : Nat := 4983230072969 + 3 ^ 40 * 3100011 * 2
def baseEnd_3100011 : Nat := 1061197118150117284270543

theorem tailTrace_3100011 : CollatzResearch.WordTrace tailWord_3100011 prefixEnd_3100011 1061197118150117284270543 := by
  unfold tailWord_3100011
  simp only [CollatzResearch.WordTrace]
  refine ⟨113066689972197061573059887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75377793314798041048706591 113066689972197061573059887)
  ·
    refine ⟨169600034958295592359589831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113066689972197061573059887 169600034958295592359589831)
    ·
      refine ⟨254400052437443388539384747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169600034958295592359589831 254400052437443388539384747)
      ·
        refine ⟨381600078656165082809077121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254400052437443388539384747 381600078656165082809077121)
        ·
          refine ⟨286200058992123812106807841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381600078656165082809077121 286200058992123812106807841)
          ·
            refine ⟨214650044244092859080105881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286200058992123812106807841 214650044244092859080105881)
            ·
              refine ⟨160987533183069644310079411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214650044244092859080105881 160987533183069644310079411)
              ·
                refine ⟨241481299774604466465119117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160987533183069644310079411 241481299774604466465119117)
                ·
                  refine ⟨90555487415476674924419669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241481299774604466465119117 90555487415476674924419669)
                  ·
                    refine ⟨1061197118150117284270543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90555487415476674924419669 1061197118150117284270543)
                    ·
                      rfl

theorem cell22_3100011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_3100011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100011 prefixEnd_3100011 := by exact prefixLift 3100011
  have htrace : WordTrace (prefixWord ++ tailWord_3100011) baseStart_3100011 baseEnd_3100011 := by
    simpa [prefixWord, tailWord_3100011, baseEnd_3100011] using wordTrace_append hprefix tailTrace_3100011
  have hstable : (prefixWord ++ tailWord_3100011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100011).length < 2 ^ (prefixWord ++ tailWord_3100011).sum := by decide
  have hdescent : baseEnd_3100011 < baseStart_3100011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100021 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 4]
def baseStart_3100021 : Nat := 118140960795 + 3100021 * 2 ^ 59
def prefixEnd_3100021 : Nat := 4983230072969 + 3 ^ 40 * 3100021 * 2
def baseEnd_3100021 : Nat := 353733513784826863840171

theorem tailTrace_3100021 : CollatzResearch.WordTrace tailWord_3100021 prefixEnd_3100021 353733513784826863840171 := by
  unfold tailWord_3100021
  simp only [CollatzResearch.WordTrace]
  refine ⟨113067054702160833280923917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75378036468107222187282611 113067054702160833280923917)
  ·
    refine ⟨42400145513310312480346469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113067054702160833280923917 42400145513310312480346469)
    ·
      refine ⟨7950027283745683590064963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42400145513310312480346469 7950027283745683590064963)
      ·
        refine ⟨11925040925618525385097445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7950027283745683590064963 11925040925618525385097445)
        ·
          refine ⟨2235945173553473509705771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11925040925618525385097445 2235945173553473509705771)
          ·
            refine ⟨3353917760330210264558657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235945173553473509705771 3353917760330210264558657)
            ·
              refine ⟨2515438320247657698418993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353917760330210264558657 2515438320247657698418993)
              ·
                refine ⟨1886578740185743273814245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515438320247657698418993 1886578740185743273814245)
                ·
                  refine ⟨353733513784826863840171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886578740185743273814245 353733513784826863840171)
                  ·
                    rfl

theorem cell22_3100021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_3100021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100021 prefixEnd_3100021 := by exact prefixLift 3100021
  have htrace : WordTrace (prefixWord ++ tailWord_3100021) baseStart_3100021 baseEnd_3100021 := by
    simpa [prefixWord, tailWord_3100021, baseEnd_3100021] using wordTrace_append hprefix tailTrace_3100021
  have hstable : (prefixWord ++ tailWord_3100021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100021).length < 2 ^ (prefixWord ++ tailWord_3100021).sum := by decide
  have hdescent : baseEnd_3100021 < baseStart_3100021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100043 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 5]
def baseStart_3100043 : Nat := 118140960795 + 3100043 * 2 ^ 59
def prefixEnd_3100043 : Nat := 4983230072969 + 3 ^ 40 * 3100043 * 2
def baseEnd_3100043 : Nat := 353736024134693289156815

theorem tailTrace_3100043 : CollatzResearch.WordTrace tailWord_3100043 prefixEnd_3100043 353736024134693289156815 := by
  unfold tailWord_3100043
  simp only [CollatzResearch.WordTrace]
  refine ⟨113067857108081131038224783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75378571405387420692149855 113067857108081131038224783)
  ·
    refine ⟨169601785662121696557337175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113067857108081131038224783 169601785662121696557337175)
    ·
      refine ⟨254402678493182544836005763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169601785662121696557337175 254402678493182544836005763)
      ·
        refine ⟨381604017739773817254008645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254402678493182544836005763 381604017739773817254008645)
        ·
          refine ⟨71550753326207590735126621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381604017739773817254008645 71550753326207590735126621)
          ·
            refine ⟨26831532497327846525672483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71550753326207590735126621 26831532497327846525672483)
            ·
              refine ⟨40247298745991769788508725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831532497327846525672483 40247298745991769788508725)
              ·
                refine ⟨3773184257436728417672693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40247298745991769788508725 3773184257436728417672693)
                ·
                  refine ⟨353736024134693289156815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3773184257436728417672693 353736024134693289156815)
                  ·
                    rfl

theorem cell22_3100043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 5].length) (baseStart_3100043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100043 prefixEnd_3100043 := by exact prefixLift 3100043
  have htrace : WordTrace (prefixWord ++ tailWord_3100043) baseStart_3100043 baseEnd_3100043 := by
    simpa [prefixWord, tailWord_3100043, baseEnd_3100043] using wordTrace_append hprefix tailTrace_3100043
  have hstable : (prefixWord ++ tailWord_3100043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100043).length < 2 ^ (prefixWord ++ tailWord_3100043).sum := by decide
  have hdescent : baseEnd_3100043 < baseStart_3100043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100058 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_3100058 : Nat := 118140960795 + 3100058 * 2 ^ 59
def prefixEnd_3100058 : Nat := 4983230072969 + 3 ^ 40 * 3100058 * 2
def baseEnd_3100058 : Nat := 1061213207210624828345399

theorem tailTrace_3100058 : CollatzResearch.WordTrace tailWord_3100058 prefixEnd_3100058 1061213207210624828345399 := by
  unfold tailWord_3100058
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267101050756697150005207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75378936135351192400013885 28267101050756697150005207)
  ·
    refine ⟨42400651576135045725007811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267101050756697150005207 42400651576135045725007811)
    ·
      refine ⟨63600977364202568587511717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42400651576135045725007811 63600977364202568587511717)
      ·
        refine ⟨11925183255787981610158447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63600977364202568587511717 11925183255787981610158447)
        ·
          refine ⟨17887774883681972415237671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11925183255787981610158447 17887774883681972415237671)
          ·
            refine ⟨26831662325522958622856507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17887774883681972415237671 26831662325522958622856507)
            ·
              refine ⟨40247493488284437934284761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26831662325522958622856507 40247493488284437934284761)
              ·
                refine ⟨30185620116213328450713571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40247493488284437934284761 30185620116213328450713571)
                ·
                  refine ⟨45278430174319992676070357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30185620116213328450713571 45278430174319992676070357)
                  ·
                    refine ⟨1061213207210624828345399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45278430174319992676070357 1061213207210624828345399)
                    ·
                      rfl

theorem cell22_3100058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_3100058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100058 prefixEnd_3100058 := by exact prefixLift 3100058
  have htrace : WordTrace (prefixWord ++ tailWord_3100058) baseStart_3100058 baseEnd_3100058 := by
    simpa [prefixWord, tailWord_3100058, baseEnd_3100058] using wordTrace_append hprefix tailTrace_3100058
  have hstable : (prefixWord ++ tailWord_3100058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100058).length < 2 ^ (prefixWord ++ tailWord_3100058).sum := by decide
  have hdescent : baseEnd_3100058 < baseStart_3100058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100077 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3100077 : Nat := 118140960795 + 3100077 * 2 ^ 59
def prefixEnd_3100077 : Nat := 4983230072969 + 3 ^ 40 * 3100077 * 2
def baseEnd_3100077 : Nat := 353739903766305037373447

theorem tailTrace_3100077 : CollatzResearch.WordTrace tailWord_3100077 prefixEnd_3100077 353739903766305037373447 := by
  unfold tailWord_3100077
  simp only [CollatzResearch.WordTrace]
  refine ⟨113069097189957954844962485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75379398126638636563308323 113069097189957954844962485)
  ·
    refine ⟨10600227861558558266715233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113069097189957954844962485 10600227861558558266715233)
    ·
      refine ⟨7950170896168918700036425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10600227861558558266715233 7950170896168918700036425)
      ·
        refine ⟨5962628172126689025027319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7950170896168918700036425 5962628172126689025027319)
        ·
          refine ⟨8943942258190033537540979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5962628172126689025027319 8943942258190033537540979)
          ·
            refine ⟨13415913387285050306311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8943942258190033537540979 13415913387285050306311469)
            ·
              refine ⟨5030967520231893864866801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13415913387285050306311469 5030967520231893864866801)
              ·
                refine ⟨3773225640173920398650101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030967520231893864866801 3773225640173920398650101)
                ·
                  refine ⟨353739903766305037373447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3773225640173920398650101 353739903766305037373447)
                  ·
                    rfl

theorem cell22_3100077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3100077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100077 prefixEnd_3100077 := by exact prefixLift 3100077
  have htrace : WordTrace (prefixWord ++ tailWord_3100077) baseStart_3100077 baseEnd_3100077 := by
    simpa [prefixWord, tailWord_3100077, baseEnd_3100077] using wordTrace_append hprefix tailTrace_3100077
  have hstable : (prefixWord ++ tailWord_3100077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100077).length < 2 ^ (prefixWord ++ tailWord_3100077).sum := by decide
  have hdescent : baseEnd_3100077 < baseStart_3100077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100088 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_3100088 : Nat := 118140960795 + 3100088 * 2 ^ 59
def prefixEnd_3100088 : Nat := 4983230072969 + 3 ^ 40 * 3100088 * 2
def baseEnd_3100088 : Nat := 353741158941238250031769

theorem tailTrace_3100088 : CollatzResearch.WordTrace tailWord_3100088 prefixEnd_3100088 353741158941238250031769 := by
  unfold tailWord_3100088
  simp only [CollatzResearch.WordTrace]
  refine ⟨56534749196459051861806459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75379665595278735815741945 56534749196459051861806459)
  ·
    refine ⟨84802123794688577792709689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56534749196459051861806459 84802123794688577792709689)
    ·
      refine ⟨63601592846016433344532267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84802123794688577792709689 63601592846016433344532267)
      ·
        refine ⟨95402389269024650016798401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63601592846016433344532267 95402389269024650016798401)
        ·
          refine ⟨71551791951768487512598801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95402389269024650016798401 71551791951768487512598801)
          ·
            refine ⟨53663843963826365634449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71551791951768487512598801 53663843963826365634449101)
            ·
              refine ⟨20123941486434887112918413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53663843963826365634449101 20123941486434887112918413)
              ·
                refine ⟨7546478057413082667344405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20123941486434887112918413 7546478057413082667344405)
                ·
                  refine ⟨353741158941238250031769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7546478057413082667344405 353741158941238250031769)
                  ·
                    rfl

theorem cell22_3100088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_3100088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100088 prefixEnd_3100088 := by exact prefixLift 3100088
  have htrace : WordTrace (prefixWord ++ tailWord_3100088) baseStart_3100088 baseEnd_3100088 := by
    simpa [prefixWord, tailWord_3100088, baseEnd_3100088] using wordTrace_append hprefix tailTrace_3100088
  have hstable : (prefixWord ++ tailWord_3100088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100088).length < 2 ^ (prefixWord ++ tailWord_3100088).sum := by decide
  have hdescent : baseEnd_3100088 < baseStart_3100088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100120 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_3100120 : Nat := 118140960795 + 3100120 * 2 ^ 59
def prefixEnd_3100120 : Nat := 4983230072969 + 3 ^ 40 * 3100120 * 2
def baseEnd_3100120 : Nat := 1061234431077677333295209

theorem tailTrace_3100120 : CollatzResearch.WordTrace tailWord_3100120 prefixEnd_3100120 1061234431077677333295209 := by
  unfold tailWord_3100120
  simp only [CollatzResearch.WordTrace]
  refine ⟨56535332764401086594388907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75380443685868115459185209 56535332764401086594388907)
  ·
    refine ⟨84802999146601629891583361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56535332764401086594388907 84802999146601629891583361)
    ·
      refine ⟨63602249359951222418687521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84802999146601629891583361 63602249359951222418687521)
      ·
        refine ⟨47701687019963416814015641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63602249359951222418687521 47701687019963416814015641)
        ·
          refine ⟨35776265264972562610511731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47701687019963416814015641 35776265264972562610511731)
          ·
            refine ⟨53664397897458843915767597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35776265264972562610511731 53664397897458843915767597)
            ·
              refine ⟨20124149211547066468412849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53664397897458843915767597 20124149211547066468412849)
              ·
                refine ⟨15093111908660299851309637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20124149211547066468412849 15093111908660299851309637)
                ·
                  refine ⟨2829958482873806222120557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15093111908660299851309637 2829958482873806222120557)
                  ·
                    refine ⟨1061234431077677333295209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829958482873806222120557 1061234431077677333295209)
                    ·
                      rfl

theorem cell22_3100120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_3100120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100120 prefixEnd_3100120 := by exact prefixLift 3100120
  have htrace : WordTrace (prefixWord ++ tailWord_3100120) baseStart_3100120 baseEnd_3100120 := by
    simpa [prefixWord, tailWord_3100120, baseEnd_3100120] using wordTrace_append hprefix tailTrace_3100120
  have hstable : (prefixWord ++ tailWord_3100120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100120).length < 2 ^ (prefixWord ++ tailWord_3100120).sum := by decide
  have hdescent : baseEnd_3100120 < baseStart_3100120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100122 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_3100122 : Nat := 118140960795 + 3100122 * 2 ^ 59
def prefixEnd_3100122 : Nat := 4983230072969 + 3 ^ 40 * 3100122 * 2
def baseEnd_3100122 : Nat := 353745038572849998248401

theorem tailTrace_3100122 : CollatzResearch.WordTrace tailWord_3100122 prefixEnd_3100122 353745038572849998248401 := by
  unfold tailWord_3100122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267684618698731882587655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75380492316529951686900413 28267684618698731882587655)
  ·
    refine ⟨42401526928048097823881483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267684618698731882587655 42401526928048097823881483)
    ·
      refine ⟨63602290392072146735822225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42401526928048097823881483 63602290392072146735822225)
      ·
        refine ⟨47701717794054110051866669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63602290392072146735822225 47701717794054110051866669)
        ·
          refine ⟨17888144172770291269450001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47701717794054110051866669 17888144172770291269450001)
          ·
            refine ⟨13416108129577718452087501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17888144172770291269450001 13416108129577718452087501)
            ·
              refine ⟨5031040548591644419532813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13416108129577718452087501 5031040548591644419532813)
              ·
                refine ⟨1886640205721866657324805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5031040548591644419532813 1886640205721866657324805)
                ·
                  refine ⟨353745038572849998248401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886640205721866657324805 353745038572849998248401)
                  ·
                    rfl

theorem cell22_3100122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_3100122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100122 prefixEnd_3100122 := by exact prefixLift 3100122
  have htrace : WordTrace (prefixWord ++ tailWord_3100122) baseStart_3100122 baseEnd_3100122 := by
    simpa [prefixWord, tailWord_3100122, baseEnd_3100122] using wordTrace_append hprefix tailTrace_3100122
  have hstable : (prefixWord ++ tailWord_3100122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100122).length < 2 ^ (prefixWord ++ tailWord_3100122).sum := by decide
  have hdescent : baseEnd_3100122 < baseStart_3100122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100135 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3100135 : Nat := 118140960795 + 3100135 * 2 ^ 59
def prefixEnd_3100135 : Nat := 4983230072969 + 3 ^ 40 * 3100135 * 2
def baseEnd_3100135 : Nat := 1061239565884222294170163

theorem tailTrace_3100135 : CollatzResearch.WordTrace tailWord_3100135 prefixEnd_3100135 1061239565884222294170163 := by
  unfold tailWord_3100135
  simp only [CollatzResearch.WordTrace]
  refine ⟨113071212623747830750573859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75380808415831887167049239 113071212623747830750573859)
  ·
    refine ⟨169606818935621746125860789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113071212623747830750573859 169606818935621746125860789)
    ·
      refine ⟨15900639275214538699299449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169606818935621746125860789 15900639275214538699299449)
      ·
        refine ⟨11925479456410904024474587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15900639275214538699299449 11925479456410904024474587)
        ·
          refine ⟨17888219184616356036711881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11925479456410904024474587 17888219184616356036711881)
          ·
            refine ⟨13416164388462267027533911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17888219184616356036711881 13416164388462267027533911)
            ·
              refine ⟨20124246582693400541300867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13416164388462267027533911 20124246582693400541300867)
              ·
                refine ⟨30186369874040100811951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20124246582693400541300867 30186369874040100811951301)
                ·
                  refine ⟨5659944351382518902240869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30186369874040100811951301 5659944351382518902240869)
                  ·
                    refine ⟨1061239565884222294170163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659944351382518902240869 1061239565884222294170163)
                    ·
                      rfl

theorem cell22_3100135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3100135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100135 prefixEnd_3100135 := by exact prefixLift 3100135
  have htrace : WordTrace (prefixWord ++ tailWord_3100135) baseStart_3100135 baseEnd_3100135 := by
    simpa [prefixWord, tailWord_3100135, baseEnd_3100135] using wordTrace_append hprefix tailTrace_3100135
  have hstable : (prefixWord ++ tailWord_3100135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100135).length < 2 ^ (prefixWord ++ tailWord_3100135).sum := by decide
  have hdescent : baseEnd_3100135 < baseStart_3100135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100150 : List Nat := [5, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3100150 : Nat := 118140960795 + 3100150 * 2 ^ 59
def prefixEnd_3100150 : Nat := 4983230072969 + 3 ^ 40 * 3100150 * 2
def baseEnd_3100150 : Nat := 117916077854529695005013

theorem tailTrace_3100150 : CollatzResearch.WordTrace tailWord_3100150 prefixEnd_3100150 117916077854529695005013 := by
  unfold tailWord_3100150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066984982418343019523119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75381173145795658874913269 7066984982418343019523119)
  ·
    refine ⟨10600477473627514529284679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7066984982418343019523119 10600477473627514529284679)
    ·
      refine ⟨15900716210441271793927019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10600477473627514529284679 15900716210441271793927019)
      ·
        refine ⟨23851074315661907690890529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15900716210441271793927019 23851074315661907690890529)
        ·
          refine ⟨17888305736746430768167897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23851074315661907690890529 17888305736746430768167897)
          ·
            refine ⟨13416229302559823076125923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17888305736746430768167897 13416229302559823076125923)
            ·
              refine ⟨20124343953839734614188885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13416229302559823076125923 20124343953839734614188885)
              ·
                refine ⟨117916077854529695005013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20124343953839734614188885 117916077854529695005013)
                ·
                  rfl

theorem cell22_3100150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3100150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100150 prefixEnd_3100150 := by exact prefixLift 3100150
  have htrace : WordTrace (prefixWord ++ tailWord_3100150) baseStart_3100150 baseEnd_3100150 := by
    simpa [prefixWord, tailWord_3100150, baseEnd_3100150] using wordTrace_append hprefix tailTrace_3100150
  have hstable : (prefixWord ++ tailWord_3100150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100150).length < 2 ^ (prefixWord ++ tailWord_3100150).sum := by decide
  have hdescent : baseEnd_3100150 < baseStart_3100150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100158 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_3100158 : Nat := 118140960795 + 3100158 * 2 ^ 59
def prefixEnd_3100158 : Nat := 4983230072969 + 3 ^ 40 * 3100158 * 2
def baseEnd_3100158 : Nat := 1061247439254257900845093

theorem tailTrace_3100158 : CollatzResearch.WordTrace tailWord_3100158 prefixEnd_3100158 1061247439254257900845093 := by
  unfold tailWord_3100158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14134006437833063209832641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75381367668443003785774085 14134006437833063209832641)
  ·
    refine ⟨10600504828374797407374481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14134006437833063209832641 10600504828374797407374481)
    ·
      refine ⟨7950378621281098055530861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10600504828374797407374481 7950378621281098055530861)
      ·
        refine ⟨2981391982980411770824073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7950378621281098055530861 2981391982980411770824073)
        ·
          refine ⟨2236043987235308828118055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981391982980411770824073 2236043987235308828118055)
          ·
            refine ⟨3354065980852963242177083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236043987235308828118055 3354065980852963242177083)
            ·
              refine ⟨5031098971279444863265625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354065980852963242177083 5031098971279444863265625)
              ·
                refine ⟨3773324228459583647449219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031098971279444863265625 3773324228459583647449219)
                ·
                  refine ⟨5659986342689375471173829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3773324228459583647449219 5659986342689375471173829)
                  ·
                    refine ⟨1061247439254257900845093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659986342689375471173829 1061247439254257900845093)
                    ·
                      rfl

theorem cell22_3100158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_3100158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100158 prefixEnd_3100158 := by exact prefixLift 3100158
  have htrace : WordTrace (prefixWord ++ tailWord_3100158) baseStart_3100158 baseEnd_3100158 := by
    simpa [prefixWord, tailWord_3100158, baseEnd_3100158] using wordTrace_append hprefix tailTrace_3100158
  have hstable : (prefixWord ++ tailWord_3100158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100158).length < 2 ^ (prefixWord ++ tailWord_3100158).sum := by decide
  have hdescent : baseEnd_3100158 < baseStart_3100158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100163 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 6]
def baseStart_3100163 : Nat := 118140960795 + 3100163 * 2 ^ 59
def prefixEnd_3100163 : Nat := 4983230072969 + 3 ^ 40 * 3100163 * 2
def baseEnd_3100163 : Nat := 1061249150856439554470077

theorem tailTrace_3100163 : CollatzResearch.WordTrace tailWord_3100163 prefixEnd_3100163 1061249150856439554470077 := by
  unfold tailWord_3100163
  simp only [CollatzResearch.WordTrace]
  refine ⟨113072233867646391532593143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75381489245097594355062095 113072233867646391532593143)
  ·
    refine ⟨169608350801469587298889715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113072233867646391532593143 169608350801469587298889715)
    ·
      refine ⟨254412526202204380948334573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169608350801469587298889715 254412526202204380948334573)
      ·
        refine ⟨95404697325826642855625465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254412526202204380948334573 95404697325826642855625465)
        ·
          refine ⟨71553522994369982141719099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95404697325826642855625465 71553522994369982141719099)
          ·
            refine ⟨107330284491554973212578649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71553522994369982141719099 107330284491554973212578649)
            ·
              refine ⟨80497713368666229909433987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107330284491554973212578649 80497713368666229909433987)
              ·
                refine ⟨120746570052999344864150981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80497713368666229909433987 120746570052999344864150981)
                ·
                  refine ⟨22639981884937377162028309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120746570052999344864150981 22639981884937377162028309)
                  ·
                    refine ⟨1061249150856439554470077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22639981884937377162028309 1061249150856439554470077)
                    ·
                      rfl

theorem cell22_3100163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_3100163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100163 prefixEnd_3100163 := by exact prefixLift 3100163
  have htrace : WordTrace (prefixWord ++ tailWord_3100163) baseStart_3100163 baseEnd_3100163 := by
    simpa [prefixWord, tailWord_3100163, baseEnd_3100163] using wordTrace_append hprefix tailTrace_3100163
  have hstable : (prefixWord ++ tailWord_3100163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100163).length < 2 ^ (prefixWord ++ tailWord_3100163).sum := by decide
  have hdescent : baseEnd_3100163 < baseStart_3100163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100165 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_3100165 : Nat := 118140960795 + 3100165 * 2 ^ 59
def prefixEnd_3100165 : Nat := 4983230072969 + 3 ^ 40 * 3100165 * 2
def baseEnd_3100165 : Nat := 1061249835497312215920071

theorem tailTrace_3100165 : CollatzResearch.WordTrace tailWord_3100165 prefixEnd_3100165 1061249835497312215920071 := by
  unfold tailWord_3100165
  simp only [CollatzResearch.WordTrace]
  refine ⟨113072306813639145874165949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75381537875759430582777299 113072306813639145874165949)
  ·
    refine ⟨42402115055114679702812231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113072306813639145874165949 42402115055114679702812231)
    ·
      refine ⟨63603172582672019554218347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42402115055114679702812231 63603172582672019554218347)
      ·
        refine ⟨95404758874008029331327521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63603172582672019554218347 95404758874008029331327521)
        ·
          refine ⟨71553569155506021998495641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95404758874008029331327521 71553569155506021998495641)
          ·
            refine ⟨53665176866629516498871731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71553569155506021998495641 53665176866629516498871731)
            ·
              refine ⟨80497765299944274748307597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53665176866629516498871731 80497765299944274748307597)
              ·
                refine ⟨30186661987479103030615349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80497765299944274748307597 30186661987479103030615349)
                ·
                  refine ⟨2829999561326165909120189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30186661987479103030615349 2829999561326165909120189)
                  ·
                    refine ⟨1061249835497312215920071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2829999561326165909120189 1061249835497312215920071)
                    ·
                      rfl

theorem cell22_3100165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_3100165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100165 prefixEnd_3100165 := by exact prefixLift 3100165
  have htrace : WordTrace (prefixWord ++ tailWord_3100165) baseStart_3100165 baseEnd_3100165 := by
    simpa [prefixWord, tailWord_3100165, baseEnd_3100165] using wordTrace_append hprefix tailTrace_3100165
  have hstable : (prefixWord ++ tailWord_3100165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100165).length < 2 ^ (prefixWord ++ tailWord_3100165).sum := by decide
  have hdescent : baseEnd_3100165 < baseStart_3100165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100246 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_3100246 : Nat := 118140960795 + 3100246 * 2 ^ 59
def prefixEnd_3100246 : Nat := 4983230072969 + 3 ^ 40 * 3100246 * 2
def baseEnd_3100246 : Nat := 353759187817551668214941

theorem tailTrace_3100246 : CollatzResearch.WordTrace tailWord_3100246 prefixEnd_3100246 353759187817551668214941 := by
  unfold tailWord_3100246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7067203820396606044241537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75383507417563797805243061 7067203820396606044241537)
  ·
    refine ⟨5300402865297454533181153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7067203820396606044241537 5300402865297454533181153)
    ·
      refine ⟨3975302148973090899885865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5300402865297454533181153 3975302148973090899885865)
      ·
        refine ⟨2981476611729818174914399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3975302148973090899885865 2981476611729818174914399)
        ·
          refine ⟨4472214917594727262371599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981476611729818174914399 4472214917594727262371599)
          ·
            refine ⟨6708322376392090893557399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472214917594727262371599 6708322376392090893557399)
            ·
              refine ⟨10062483564588136340336099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708322376392090893557399 10062483564588136340336099)
              ·
                refine ⟨15093725346882204510504149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10062483564588136340336099 15093725346882204510504149)
                ·
                  refine ⟨353759187817551668214941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15093725346882204510504149 353759187817551668214941)
                  ·
                    rfl

theorem cell22_3100246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_3100246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100246 prefixEnd_3100246 := by exact prefixLift 3100246
  have htrace : WordTrace (prefixWord ++ tailWord_3100246) baseStart_3100246 baseEnd_3100246 := by
    simpa [prefixWord, tailWord_3100246, baseEnd_3100246] using wordTrace_append hprefix tailTrace_3100246
  have hstable : (prefixWord ++ tailWord_3100246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100246).length < 2 ^ (prefixWord ++ tailWord_3100246).sum := by decide
  have hdescent : baseEnd_3100246 < baseStart_3100246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100257 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 4]
def baseStart_3100257 : Nat := 118140960795 + 3100257 * 2 ^ 59
def prefixEnd_3100257 : Nat := 4983230072969 + 3 ^ 40 * 3100257 * 2
def baseEnd_3100257 : Nat := 353760442992484880873263

theorem tailTrace_3100257 : CollatzResearch.WordTrace tailWord_3100257 prefixEnd_3100257 353760442992484880873263 := by
  unfold tailWord_3100257
  simp only [CollatzResearch.WordTrace]
  refine ⟨113075662329305845586515025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75383774886203897057676683 113075662329305845586515025)
  ·
    refine ⟨84806746746979384189886269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113075662329305845586515025 84806746746979384189886269)
    ·
      refine ⟨31802530030117269071207351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84806746746979384189886269 31802530030117269071207351)
      ·
        refine ⟨47703795045175903606811027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31802530030117269071207351 47703795045175903606811027)
        ·
          refine ⟨71555692567763855410216541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47703795045175903606811027 71555692567763855410216541)
          ·
            refine ⟨26833384712911445778831203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71555692567763855410216541 26833384712911445778831203)
            ·
              refine ⟨40250077069367168668246805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26833384712911445778831203 40250077069367168668246805)
              ·
                refine ⟨1886722362626586031324069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40250077069367168668246805 1886722362626586031324069)
                ·
                  refine ⟨353760442992484880873263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886722362626586031324069 353760442992484880873263)
                  ·
                    rfl

theorem cell22_3100257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_3100257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100257 prefixEnd_3100257 := by exact prefixLift 3100257
  have htrace : WordTrace (prefixWord ++ tailWord_3100257) baseStart_3100257 baseEnd_3100257 := by
    simpa [prefixWord, tailWord_3100257, baseEnd_3100257] using wordTrace_append hprefix tailTrace_3100257
  have hstable : (prefixWord ++ tailWord_3100257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100257).length < 2 ^ (prefixWord ++ tailWord_3100257).sum := by decide
  have hdescent : baseEnd_3100257 < baseStart_3100257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100272 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_3100272 : Nat := 118140960795 + 3100272 * 2 ^ 59
def prefixEnd_3100272 : Nat := 4983230072969 + 3 ^ 40 * 3100272 * 2
def baseEnd_3100272 : Nat := 1061286463783999603494743

theorem tailTrace_3100272 : CollatzResearch.WordTrace tailWord_3100272 prefixEnd_3100272 1061286463783999603494743 := by
  unfold tailWord_3100272
  simp only [CollatzResearch.WordTrace]
  refine ⟨56538104712125751574155535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75384139616167668765540713 56538104712125751574155535)
  ·
    refine ⟨84807157068188627361233303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56538104712125751574155535 84807157068188627361233303)
    ·
      refine ⟨127210735602282941041849955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84807157068188627361233303 127210735602282941041849955)
      ·
        refine ⟨190816103403424411562774933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127210735602282941041849955 190816103403424411562774933)
        ·
          refine ⟨8944504847035519292005075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190816103403424411562774933 8944504847035519292005075)
          ·
            refine ⟨13416757270553278938007613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944504847035519292005075 13416757270553278938007613)
            ·
              refine ⟨5031283976457479601752855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13416757270553278938007613 5031283976457479601752855)
              ·
                refine ⟨7546925964686219402629283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031283976457479601752855 7546925964686219402629283)
                ·
                  refine ⟨11320388947029329103943925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546925964686219402629283 11320388947029329103943925)
                  ·
                    refine ⟨1061286463783999603494743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11320388947029329103943925 1061286463783999603494743)
                    ·
                      rfl

theorem cell22_3100272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_3100272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100272 prefixEnd_3100272 := by exact prefixLift 3100272
  have htrace : WordTrace (prefixWord ++ tailWord_3100272) baseStart_3100272 baseEnd_3100272 := by
    simpa [prefixWord, tailWord_3100272, baseEnd_3100272] using wordTrace_append hprefix tailTrace_3100272
  have hstable : (prefixWord ++ tailWord_3100272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100272).length < 2 ^ (prefixWord ++ tailWord_3100272).sum := by decide
  have hdescent : baseEnd_3100272 < baseStart_3100272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100302 : List Nat := [4, 1, 1, 3, 1, 4, 8]
def baseStart_3100302 : Nat := 118140960795 + 3100302 * 2 ^ 59
def prefixEnd_3100302 : Nat := 4983230072969 + 3 ^ 40 * 3100302 * 2
def baseEnd_3100302 : Nat := 39307286422114426860913

theorem tailTrace_3100302 : CollatzResearch.WordTrace tailWord_3100302 prefixEnd_3100302 39307286422114426860913 := by
  unfold tailWord_3100302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14134662951767852283987895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75384869076095212181268773 14134662951767852283987895)
  ·
    refine ⟨21201994427651778425981843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14134662951767852283987895 21201994427651778425981843)
    ·
      refine ⟨31802991641477667638972765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21201994427651778425981843 31802991641477667638972765)
      ·
        refine ⟨11926121865554125364614787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31802991641477667638972765 11926121865554125364614787)
        ·
          refine ⟨17889182798331188046922181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11926121865554125364614787 17889182798331188046922181)
          ·
            refine ⟨3354221774687097758797909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17889182798331188046922181 3354221774687097758797909)
            ·
              refine ⟨39307286422114426860913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3354221774687097758797909 39307286422114426860913)
              ·
                rfl

theorem cell22_3100302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 8].length) (baseStart_3100302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100302 prefixEnd_3100302 := by exact prefixLift 3100302
  have htrace : WordTrace (prefixWord ++ tailWord_3100302) baseStart_3100302 baseEnd_3100302 := by
    simpa [prefixWord, tailWord_3100302, baseEnd_3100302] using wordTrace_append hprefix tailTrace_3100302
  have hstable : (prefixWord ++ tailWord_3100302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100302).length < 2 ^ (prefixWord ++ tailWord_3100302).sum := by decide
  have hdescent : baseEnd_3100302 < baseStart_3100302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100308 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3100308 : Nat := 118140960795 + 3100308 * 2 ^ 59
def prefixEnd_3100308 : Nat := 4983230072969 + 3 ^ 40 * 3100308 * 2
def baseEnd_3100308 : Nat := 353766262439902503198211

theorem tailTrace_3100308 : CollatzResearch.WordTrace tailWord_3100308 prefixEnd_3100308 353766262439902503198211 := by
  unfold tailWord_3100308
  simp only [CollatzResearch.WordTrace]
  refine ⟨56538761226060540648310789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75385014968080720864414385 56538761226060540648310789)
  ·
    refine ⟨10601017729886351371558273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56538761226060540648310789 10601017729886351371558273)
    ·
      refine ⟨7950763297414763528668705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10601017729886351371558273 7950763297414763528668705)
      ·
        refine ⟨5963072473061072646501529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7950763297414763528668705 5963072473061072646501529)
        ·
          refine ⟨4472304354795804484876147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5963072473061072646501529 4472304354795804484876147)
          ·
            refine ⟨6708456532193706727314221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472304354795804484876147 6708456532193706727314221)
            ·
              refine ⟨2515671199572640022742833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6708456532193706727314221 2515671199572640022742833)
              ·
                refine ⟨1886753399679480017057125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515671199572640022742833 1886753399679480017057125)
                ·
                  refine ⟨353766262439902503198211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886753399679480017057125 353766262439902503198211)
                  ·
                    rfl

theorem cell22_3100308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3100308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100308 prefixEnd_3100308 := by exact prefixLift 3100308
  have htrace : WordTrace (prefixWord ++ tailWord_3100308) baseStart_3100308 baseEnd_3100308 := by
    simpa [prefixWord, tailWord_3100308, baseEnd_3100308] using wordTrace_append hprefix tailTrace_3100308
  have hstable : (prefixWord ++ tailWord_3100308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100308).length < 2 ^ (prefixWord ++ tailWord_3100308).sum := by decide
  have hdescent : baseEnd_3100308 < baseStart_3100308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100319 : List Nat := [1, 1, 2, 7, 1, 1, 2, 7]
def baseStart_3100319 : Nat := 118140960795 + 3100319 * 2 ^ 59
def prefixEnd_3100319 : Nat := 4983230072969 + 3 ^ 40 * 3100319 * 2
def baseEnd_3100319 : Nat := 117922505871611905285511

theorem tailTrace_3100319 : CollatzResearch.WordTrace tailWord_3100319 prefixEnd_3100319 117922505871611905285511 := by
  unfold tailWord_3100319
  simp only [CollatzResearch.WordTrace]
  refine ⟨113077923655081230175272011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75385282436720820116848007 113077923655081230175272011)
  ·
    refine ⟨169616885482621845262908017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113077923655081230175272011 169616885482621845262908017)
    ·
      refine ⟨127212664111966383947181013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169616885482621845262908017 127212664111966383947181013)
      ·
        refine ⟨2981546815124212123762055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 127212664111966383947181013 2981546815124212123762055)
        ·
          refine ⟨4472320222686318185643083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981546815124212123762055 4472320222686318185643083)
          ·
            refine ⟨6708480334029477278464625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472320222686318185643083 6708480334029477278464625)
            ·
              refine ⟨5031360250522107958848469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708480334029477278464625 5031360250522107958848469)
              ·
                refine ⟨117922505871611905285511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5031360250522107958848469 117922505871611905285511)
                ·
                  rfl

theorem cell22_3100319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 7].length) (baseStart_3100319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100319 prefixEnd_3100319 := by exact prefixLift 3100319
  have htrace : WordTrace (prefixWord ++ tailWord_3100319) baseStart_3100319 baseEnd_3100319 := by
    simpa [prefixWord, tailWord_3100319, baseEnd_3100319] using wordTrace_append hprefix tailTrace_3100319
  have hstable : (prefixWord ++ tailWord_3100319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100319).length < 2 ^ (prefixWord ++ tailWord_3100319).sum := by decide
  have hdescent : baseEnd_3100319 < baseStart_3100319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100377 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_3100377 : Nat := 118140960795 + 3100377 * 2 ^ 59
def prefixEnd_3100377 : Nat := 4983230072969 + 3 ^ 40 * 3100377 * 2
def baseEnd_3100377 : Nat := 1061322407429814329619421

theorem tailTrace_3100377 : CollatzResearch.WordTrace tailWord_3100377 prefixEnd_3100377 1061322407429814329619421 := by
  unfold tailWord_3100377
  simp only [CollatzResearch.WordTrace]
  refine ⟨113080039088871106080883385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75386692725914070720588923 113080039088871106080883385)
  ·
    refine ⟨84810029316653329560662539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113080039088871106080883385 84810029316653329560662539)
    ·
      refine ⟨127215043974979994340993809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84810029316653329560662539 127215043974979994340993809)
      ·
        refine ⟨95411282981234995755745357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127215043974979994340993809 95411282981234995755745357)
        ·
          refine ⟨35779231117963123408404509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95411282981234995755745357 35779231117963123408404509)
          ·
            refine ⟨13417211669236171278151691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35779231117963123408404509 13417211669236171278151691)
            ·
              refine ⟨20125817503854256917227537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417211669236171278151691 20125817503854256917227537)
              ·
                refine ⟨15094363127890692687920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20125817503854256917227537 15094363127890692687920653)
                ·
                  refine ⟨5660386172959009757970245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15094363127890692687920653 5660386172959009757970245)
                  ·
                    refine ⟨1061322407429814329619421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5660386172959009757970245 1061322407429814329619421)
                    ·
                      rfl

theorem cell22_3100377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_3100377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100377 prefixEnd_3100377 := by exact prefixLift 3100377
  have htrace : WordTrace (prefixWord ++ tailWord_3100377) baseStart_3100377 baseEnd_3100377 := by
    simpa [prefixWord, tailWord_3100377, baseEnd_3100377] using wordTrace_append hprefix tailTrace_3100377
  have hstable : (prefixWord ++ tailWord_3100377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100377).length < 2 ^ (prefixWord ++ tailWord_3100377).sum := by decide
  have hdescent : baseEnd_3100377 < baseStart_3100377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100392 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_3100392 : Nat := 118140960795 + 3100392 * 2 ^ 59
def prefixEnd_3100392 : Nat := 4983230072969 + 3 ^ 40 * 3100392 * 2
def baseEnd_3100392 : Nat := 353775847412119763498125

theorem tailTrace_3100392 : CollatzResearch.WordTrace tailWord_3100392 prefixEnd_3100392 353775847412119763498125 := by
  unfold tailWord_3100392
  simp only [CollatzResearch.WordTrace]
  refine ⟨56540293091908381821339715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75387057455877842428452953 56540293091908381821339715)
  ·
    refine ⟨84810439637862572732009573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56540293091908381821339715 84810439637862572732009573)
    ·
      refine ⟨15901957432099232387251795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84810439637862572732009573 15901957432099232387251795)
      ·
        refine ⟨23852936148148848580877693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15901957432099232387251795 23852936148148848580877693)
        ·
          refine ⟨8944851055555818217829135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23852936148148848580877693 8944851055555818217829135)
          ·
            refine ⟨13417276583333727326743703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944851055555818217829135 13417276583333727326743703)
            ·
              refine ⟨20125914875000590990115555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417276583333727326743703 20125914875000590990115555)
              ·
                refine ⟨30188872312500886485173333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20125914875000590990115555 30188872312500886485173333)
                ·
                  refine ⟨353775847412119763498125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30188872312500886485173333 353775847412119763498125)
                  ·
                    rfl

theorem cell22_3100392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_3100392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100392 prefixEnd_3100392 := by exact prefixLift 3100392
  have htrace : WordTrace (prefixWord ++ tailWord_3100392) baseStart_3100392 baseEnd_3100392 := by
    simpa [prefixWord, tailWord_3100392, baseEnd_3100392] using wordTrace_append hprefix tailTrace_3100392
  have hstable : (prefixWord ++ tailWord_3100392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100392).length < 2 ^ (prefixWord ++ tailWord_3100392).sum := by decide
  have hdescent : baseEnd_3100392 < baseStart_3100392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100407 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3100407 : Nat := 118140960795 + 3100407 * 2 ^ 59
def prefixEnd_3100407 : Nat := 4983230072969 + 3 ^ 40 * 3100407 * 2
def baseEnd_3100407 : Nat := 1061332677042904251369329

theorem tailTrace_3100407 : CollatzResearch.WordTrace tailWord_3100407 prefixEnd_3100407 1061332677042904251369329 := by
  unfold tailWord_3100407
  simp only [CollatzResearch.WordTrace]
  refine ⟨113081133278762421204475475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75387422185841614136316983 113081133278762421204475475)
  ·
    refine ⟨169621699918143631806713213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113081133278762421204475475 169621699918143631806713213)
    ·
      refine ⟨63608137469303861927517455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169621699918143631806713213 63608137469303861927517455)
      ·
        refine ⟨95412206203955792891276183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63608137469303861927517455 95412206203955792891276183)
        ·
          refine ⟨143118309305933689336914275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95412206203955792891276183 143118309305933689336914275)
          ·
            refine ⟨214677463958900534005371413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143118309305933689336914275 214677463958900534005371413)
            ·
              refine ⟨10063006123073462531501785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214677463958900534005371413 10063006123073462531501785)
              ·
                refine ⟨7547254592305096898626339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10063006123073462531501785 7547254592305096898626339)
                ·
                  refine ⟨11320881888457645347939509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547254592305096898626339 11320881888457645347939509)
                  ·
                    refine ⟨1061332677042904251369329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11320881888457645347939509 1061332677042904251369329)
                    ·
                      rfl

theorem cell22_3100407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3100407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100407 prefixEnd_3100407 := by exact prefixLift 3100407
  have htrace : WordTrace (prefixWord ++ tailWord_3100407) baseStart_3100407 baseEnd_3100407 := by
    simpa [prefixWord, tailWord_3100407, baseEnd_3100407] using wordTrace_append hprefix tailTrace_3100407
  have hstable : (prefixWord ++ tailWord_3100407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100407).length < 2 ^ (prefixWord ++ tailWord_3100407).sum := by decide
  have hdescent : baseEnd_3100407 < baseStart_3100407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100424 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_3100424 : Nat := 118140960795 + 3100424 * 2 ^ 59
def prefixEnd_3100424 : Nat := 4983230072969 + 3 ^ 40 * 3100424 * 2
def baseEnd_3100424 : Nat := 1061338496490321873694277

theorem tailTrace_3100424 : CollatzResearch.WordTrace tailWord_3100424 prefixEnd_3100424 1061338496490321873694277 := by
  unfold tailWord_3100424
  simp only [CollatzResearch.WordTrace]
  refine ⟨56540876659850416553922163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75387835546467222071896217 56540876659850416553922163)
  ·
    refine ⟨84811314989775624830883245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56540876659850416553922163 84811314989775624830883245)
    ·
      refine ⟨31804243121165859311581217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84811314989775624830883245 31804243121165859311581217)
      ·
        refine ⟨23853182340874394483685913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31804243121165859311581217 23853182340874394483685913)
        ·
          refine ⟨17889886755655795862764435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23853182340874394483685913 17889886755655795862764435)
          ·
            refine ⟨26834830133483693794146653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17889886755655795862764435 26834830133483693794146653)
            ·
              refine ⟨10063061300056385172804995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26834830133483693794146653 10063061300056385172804995)
              ·
                refine ⟨15094591950084577759207493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10063061300056385172804995 15094591950084577759207493)
                ·
                  refine ⟨2830235990640858329851405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15094591950084577759207493 2830235990640858329851405)
                  ·
                    refine ⟨1061338496490321873694277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830235990640858329851405 1061338496490321873694277)
                    ·
                      rfl

theorem cell22_3100424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_3100424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100424 prefixEnd_3100424 := by exact prefixLift 3100424
  have htrace : WordTrace (prefixWord ++ tailWord_3100424) baseStart_3100424 baseEnd_3100424 := by
    simpa [prefixWord, tailWord_3100424, baseEnd_3100424] using wordTrace_append hprefix tailTrace_3100424
  have hstable : (prefixWord ++ tailWord_3100424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100424).length < 2 ^ (prefixWord ++ tailWord_3100424).sum := by decide
  have hdescent : baseEnd_3100424 < baseStart_3100424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100593 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_3100593 : Nat := 118140960795 + 3100593 * 2 ^ 59
def prefixEnd_3100593 : Nat := 4983230072969 + 3 ^ 40 * 3100593 * 2
def baseEnd_3100593 : Nat := 1061396348644061766218759

theorem tailTrace_3100593 : CollatzResearch.WordTrace tailWord_3100593 prefixEnd_3100593 1061396348644061766218759 := by
  unfold tailWord_3100593
  simp only [CollatzResearch.WordTrace]
  refine ⟨113087917256088574970746433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75391944837392383313830955 113087917256088574970746433)
  ·
    refine ⟨84815937942066431228059825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113087917256088574970746433 84815937942066431228059825)
    ·
      refine ⟨63611953456549823421044869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84815937942066431228059825 63611953456549823421044869)
      ·
        refine ⟨11927241273103091891445913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63611953456549823421044869 11927241273103091891445913)
        ·
          refine ⟨8945430954827318918584435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11927241273103091891445913 8945430954827318918584435)
          ·
            refine ⟨13418146432240978377876653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8945430954827318918584435 13418146432240978377876653)
            ·
              refine ⟨5031804912090366891703745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13418146432240978377876653 5031804912090366891703745)
              ·
                refine ⟨3773853684067775168777809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5031804912090366891703745 3773853684067775168777809)
                ·
                  refine ⟨2830390263050831376583357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3773853684067775168777809 2830390263050831376583357)
                  ·
                    refine ⟨1061396348644061766218759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830390263050831376583357 1061396348644061766218759)
                    ·
                      rfl

theorem cell22_3100593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_3100593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100593 prefixEnd_3100593 := by exact prefixLift 3100593
  have htrace : WordTrace (prefixWord ++ tailWord_3100593) baseStart_3100593 baseEnd_3100593 := by
    simpa [prefixWord, tailWord_3100593, baseEnd_3100593] using wordTrace_append hprefix tailTrace_3100593
  have hstable : (prefixWord ++ tailWord_3100593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100593).length < 2 ^ (prefixWord ++ tailWord_3100593).sum := by decide
  have hdescent : baseEnd_3100593 < baseStart_3100593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100655 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 1, 3]
def baseStart_3100655 : Nat := 118140960795 + 3100655 * 2 ^ 59
def prefixEnd_3100655 : Nat := 4983230072969 + 3 ^ 40 * 3100655 * 2
def baseEnd_3100655 : Nat := 1061417572511114271168569

theorem tailTrace_3100655 : CollatzResearch.WordTrace tailWord_3100655 prefixEnd_3100655 1061417572511114271168569 := by
  unfold tailWord_3100655
  simp only [CollatzResearch.WordTrace]
  refine ⟨113090178581863959559503419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75393452387909306373002279 113090178581863959559503419)
  ·
    refine ⟨169635267872795939339255129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113090178581863959559503419 169635267872795939339255129)
    ·
      refine ⟨127226450904596954504441347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169635267872795939339255129 127226450904596954504441347)
      ·
        refine ⟨190839676356895431756662021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127226450904596954504441347 190839676356895431756662021)
        ·
          refine ⟨35782439316917893454374129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190839676356895431756662021 35782439316917893454374129)
          ·
            refine ⟨26836829487688420090780597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35782439316917893454374129 26836829487688420090780597)
            ·
              refine ⟨2515952764470789383510681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26836829487688420090780597 2515952764470789383510681)
              ·
                refine ⟨1886964573353092037633011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515952764470789383510681 1886964573353092037633011)
                ·
                  refine ⟨2830446860029638056449517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886964573353092037633011 2830446860029638056449517)
                  ·
                    refine ⟨1061417572511114271168569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830446860029638056449517 1061417572511114271168569)
                    ·
                      rfl

theorem cell22_3100655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_3100655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100655 prefixEnd_3100655 := by exact prefixLift 3100655
  have htrace : WordTrace (prefixWord ++ tailWord_3100655) baseStart_3100655 baseEnd_3100655 := by
    simpa [prefixWord, tailWord_3100655, baseEnd_3100655] using wordTrace_append hprefix tailTrace_3100655
  have hstable : (prefixWord ++ tailWord_3100655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100655).length < 2 ^ (prefixWord ++ tailWord_3100655).sum := by decide
  have hdescent : baseEnd_3100655 < baseStart_3100655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100728 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_3100728 : Nat := 118140960795 + 3100728 * 2 ^ 59
def prefixEnd_3100728 : Nat := 4983230072969 + 3 ^ 40 * 3100728 * 2
def baseEnd_3100728 : Nat := 1061442561902966414093345

theorem tailTrace_3100728 : CollatzResearch.WordTrace tailWord_3100728 prefixEnd_3100728 1061442561902966414093345 := by
  unfold tailWord_3100728
  simp only [CollatzResearch.WordTrace]
  refine ⟨56546420555299746513455419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75395227407066328684607225 56546420555299746513455419)
  ·
    refine ⟨84819630832949619770183129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56546420555299746513455419 84819630832949619770183129)
    ·
      refine ⟨63614723124712214827637347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84819630832949619770183129 63614723124712214827637347)
      ·
        refine ⟨95422084687068322241456021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63614723124712214827637347 95422084687068322241456021)
        ·
          refine ⟨4472910219706327605068251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 95422084687068322241456021 4472910219706327605068251)
          ·
            refine ⟨6709365329559491407602377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472910219706327605068251 6709365329559491407602377)
            ·
              refine ⟨5032023997169618555701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6709365329559491407602377 5032023997169618555701783)
              ·
                refine ⟨7548035995754427833552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032023997169618555701783 7548035995754427833552675)
                ·
                  refine ⟨11322053993631641750329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548035995754427833552675 11322053993631641750329013)
                  ·
                    refine ⟨1061442561902966414093345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11322053993631641750329013 1061442561902966414093345)
                    ·
                      rfl

theorem cell22_3100728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_3100728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100728 prefixEnd_3100728 := by exact prefixLift 3100728
  have htrace : WordTrace (prefixWord ++ tailWord_3100728) baseStart_3100728 baseEnd_3100728 := by
    simpa [prefixWord, tailWord_3100728, baseEnd_3100728] using wordTrace_append hprefix tailTrace_3100728
  have hstable : (prefixWord ++ tailWord_3100728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100728).length < 2 ^ (prefixWord ++ tailWord_3100728).sum := by decide
  have hdescent : baseEnd_3100728 < baseStart_3100728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100739 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_3100739 : Nat := 118140960795 + 3100739 * 2 ^ 59
def prefixEnd_3100739 : Nat := 4983230072969 + 3 ^ 40 * 3100739 * 2
def baseEnd_3100739 : Nat := 1061446327427766052068311

theorem tailTrace_3100739 : CollatzResearch.WordTrace tailWord_3100739 prefixEnd_3100739 1061446327427766052068311 := by
  unfold tailWord_3100739
  simp only [CollatzResearch.WordTrace]
  refine ⟨113093242313559641905561271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75395494875706427937040847 113093242313559641905561271)
  ·
    refine ⟨169639863470339462858341907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113093242313559641905561271 169639863470339462858341907)
    ·
      refine ⟨254459795205509194287512861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169639863470339462858341907 254459795205509194287512861)
      ·
        refine ⟨95422423202065947857817323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254459795205509194287512861 95422423202065947857817323)
        ·
          refine ⟨143133634803098921786725985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95422423202065947857817323 143133634803098921786725985)
          ·
            refine ⟨107350226102324191340044489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143133634803098921786725985 107350226102324191340044489)
            ·
              refine ⟨80512669576743143505033367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107350226102324191340044489 80512669576743143505033367)
              ·
                refine ⟨120769004365114715257550051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80512669576743143505033367 120769004365114715257550051)
                ·
                  refine ⟨181153506547672072886325077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120769004365114715257550051 181153506547672072886325077)
                  ·
                    refine ⟨1061446327427766052068311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181153506547672072886325077 1061446327427766052068311)
                    ·
                      rfl

theorem cell22_3100739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_3100739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100739 prefixEnd_3100739 := by exact prefixLift 3100739
  have htrace : WordTrace (prefixWord ++ tailWord_3100739) baseStart_3100739 baseEnd_3100739 := by
    simpa [prefixWord, tailWord_3100739, baseEnd_3100739] using wordTrace_append hprefix tailTrace_3100739
  have hstable : (prefixWord ++ tailWord_3100739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100739).length < 2 ^ (prefixWord ++ tailWord_3100739).sum := by decide
  have hdescent : baseEnd_3100739 < baseStart_3100739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100773 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_3100773 : Nat := 118140960795 + 3100773 * 2 ^ 59
def prefixEnd_3100773 : Nat := 4983230072969 + 3 ^ 40 * 3100773 * 2
def baseEnd_3100773 : Nat := 1061457966322601296718207

theorem tailTrace_3100773 : CollatzResearch.WordTrace tailWord_3100773 prefixEnd_3100773 1061457966322601296718207 := by
  unfold tailWord_3100773
  simp only [CollatzResearch.WordTrace]
  refine ⟨113094482395436465712298973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75396321596957643808199315 113094482395436465712298973)
  ·
    refine ⟨42410430898288674642112115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113094482395436465712298973 42410430898288674642112115)
    ·
      refine ⟨63615646347433011963168173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42410430898288674642112115 63615646347433011963168173)
      ·
        refine ⟨23855867380287379486188065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63615646347433011963168173 23855867380287379486188065)
        ·
          refine ⟨17891900535215534614641049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23855867380287379486188065 17891900535215534614641049)
          ·
            refine ⟨13418925401411650960980787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17891900535215534614641049 13418925401411650960980787)
            ·
              refine ⟨20128388102117476441471181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13418925401411650960980787 20128388102117476441471181)
              ·
                refine ⟨7548145538294053665551693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20128388102117476441471181 7548145538294053665551693)
                ·
                  refine ⟨2830554576860270124581885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7548145538294053665551693 2830554576860270124581885)
                  ·
                    refine ⟨1061457966322601296718207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830554576860270124581885 1061457966322601296718207)
                    ·
                      rfl

theorem cell22_3100773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_3100773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100773 prefixEnd_3100773 := by exact prefixLift 3100773
  have htrace : WordTrace (prefixWord ++ tailWord_3100773) baseStart_3100773 baseEnd_3100773 := by
    simpa [prefixWord, tailWord_3100773, baseEnd_3100773] using wordTrace_append hprefix tailTrace_3100773
  have hstable : (prefixWord ++ tailWord_3100773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100773).length < 2 ^ (prefixWord ++ tailWord_3100773).sum := by decide
  have hdescent : baseEnd_3100773 < baseStart_3100773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100790 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3100790 : Nat := 118140960795 + 3100790 * 2 ^ 59
def prefixEnd_3100790 : Nat := 4983230072969 + 3 ^ 40 * 3100790 * 2
def baseEnd_3100790 : Nat := 1061463785770018919043155

theorem tailTrace_3100790 : CollatzResearch.WordTrace tailWord_3100790 prefixEnd_3100790 1061463785770018919043155 := by
  unfold tailWord_3100790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068443902273429850979239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75396734957583251743778549 7068443902273429850979239)
  ·
    refine ⟨10602665853410144776468859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7068443902273429850979239 10602665853410144776468859)
    ·
      refine ⟨15903998780115217164703289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10602665853410144776468859 15903998780115217164703289)
      ·
        refine ⟨11927999085086412873527467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15903998780115217164703289 11927999085086412873527467)
        ·
          refine ⟨17891998627629619310291201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11927999085086412873527467 17891998627629619310291201)
          ·
            refine ⟨13418998970722214482718401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17891998627629619310291201 13418998970722214482718401)
            ·
              refine ⟨10064249228041660862038801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13418998970722214482718401 10064249228041660862038801)
              ·
                refine ⟨7548186921031245646529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10064249228041660862038801 7548186921031245646529101)
                ·
                  refine ⟨2830570095386717117448413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7548186921031245646529101 2830570095386717117448413)
                  ·
                    refine ⟨1061463785770018919043155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830570095386717117448413 1061463785770018919043155)
                    ·
                      rfl

theorem cell22_3100790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3100790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100790 prefixEnd_3100790 := by exact prefixLift 3100790
  have htrace : WordTrace (prefixWord ++ tailWord_3100790) baseStart_3100790 baseEnd_3100790 := by
    simpa [prefixWord, tailWord_3100790, baseEnd_3100790] using wordTrace_append hprefix tailTrace_3100790
  have hstable : (prefixWord ++ tailWord_3100790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100790).length < 2 ^ (prefixWord ++ tailWord_3100790).sum := by decide
  have hdescent : baseEnd_3100790 < baseStart_3100790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100824 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 1, 3]
def baseStart_3100824 : Nat := 118140960795 + 3100824 * 2 ^ 59
def prefixEnd_3100824 : Nat := 4983230072969 + 3 ^ 40 * 3100824 * 2
def baseEnd_3100824 : Nat := 1061475424664854163693051

theorem tailTrace_3100824 : CollatzResearch.WordTrace tailWord_3100824 prefixEnd_3100824 1061475424664854163693051 := by
  unfold tailWord_3100824
  simp only [CollatzResearch.WordTrace]
  refine ⟨56548171259125850711202763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75397561678834467614937017 56548171259125850711202763)
  ·
    refine ⟨84822256888688776066804145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56548171259125850711202763 84822256888688776066804145)
    ·
      refine ⟨63616692666516582050103109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84822256888688776066804145 63616692666516582050103109)
      ·
        refine ⟨11928129874971859134394333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63616692666516582050103109 11928129874971859134394333)
        ·
          refine ⟨4473048703114447175397875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11928129874971859134394333 4473048703114447175397875)
          ·
            refine ⟨6709573054671670763096813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473048703114447175397875 6709573054671670763096813)
            ·
              refine ⟨2516089895501876536161305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6709573054671670763096813 2516089895501876536161305)
              ·
                refine ⟨1887067421626407402120979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516089895501876536161305 1887067421626407402120979)
                ·
                  refine ⟨2830601132439611103181469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887067421626407402120979 2830601132439611103181469)
                  ·
                    refine ⟨1061475424664854163693051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830601132439611103181469 1061475424664854163693051)
                    ·
                      rfl

theorem cell22_3100824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_3100824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100824 prefixEnd_3100824 := by exact prefixLift 3100824
  have htrace : WordTrace (prefixWord ++ tailWord_3100824) baseStart_3100824 baseEnd_3100824 := by
    simpa [prefixWord, tailWord_3100824, baseEnd_3100824] using wordTrace_append hprefix tailTrace_3100824
  have hstable : (prefixWord ++ tailWord_3100824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100824).length < 2 ^ (prefixWord ++ tailWord_3100824).sum := by decide
  have hdescent : baseEnd_3100824 < baseStart_3100824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100882 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3100882 : Nat := 118140960795 + 3100882 * 2 ^ 59
def prefixEnd_3100882 : Nat := 4983230072969 + 3 ^ 40 * 3100882 * 2
def baseEnd_3100882 : Nat := 353831759750053781914291

theorem tailTrace_3100882 : CollatzResearch.WordTrace tailWord_3100882 prefixEnd_3100882 353831759750053781914291 := by
  unfold tailWord_3100882
  simp only [CollatzResearch.WordTrace]
  refine ⟨28274614488010394332004225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75398971968027718218677933 28274614488010394332004225)
  ·
    refine ⟨21205960866007795749003169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28274614488010394332004225 21205960866007795749003169)
    ·
      refine ⟨15904470649505846811752377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21205960866007795749003169 15904470649505846811752377)
      ·
        refine ⟨11928352987129385108814283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15904470649505846811752377 11928352987129385108814283)
        ·
          refine ⟨17892529480694077663221425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11928352987129385108814283 17892529480694077663221425)
          ·
            refine ⟨13419397110520558247416069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17892529480694077663221425 13419397110520558247416069)
            ·
              refine ⟨2516136958222604671390513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13419397110520558247416069 2516136958222604671390513)
              ·
                refine ⟨1887102718666953503542885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516136958222604671390513 1887102718666953503542885)
                ·
                  refine ⟨353831759750053781914291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887102718666953503542885 353831759750053781914291)
                  ·
                    rfl

theorem cell22_3100882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3100882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100882 prefixEnd_3100882 := by exact prefixLift 3100882
  have htrace : WordTrace (prefixWord ++ tailWord_3100882) baseStart_3100882 baseEnd_3100882 := by
    simpa [prefixWord, tailWord_3100882, baseEnd_3100882] using wordTrace_append hprefix tailTrace_3100882
  have hstable : (prefixWord ++ tailWord_3100882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100882).length < 2 ^ (prefixWord ++ tailWord_3100882).sum := by decide
  have hdescent : baseEnd_3100882 < baseStart_3100882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3100942 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3100942 : Nat := 118140960795 + 3100942 * 2 ^ 59
def prefixEnd_3100942 : Nat := 4983230072969 + 3 ^ 40 * 3100942 * 2
def baseEnd_3100942 : Nat := 1061515818476341189242689

theorem tailTrace_3100942 : CollatzResearch.WordTrace tailWord_3100942 prefixEnd_3100942 1061515818476341189242689 := by
  unfold tailWord_3100942
  simp only [CollatzResearch.WordTrace]
  refine ⟨14137580791478025946900135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75400430887882805050134053 14137580791478025946900135)
  ·
    refine ⟨21206371187217038920350203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14137580791478025946900135 21206371187217038920350203)
    ·
      refine ⟨31809556780825558380525305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21206371187217038920350203 31809556780825558380525305)
      ·
        refine ⟨23857167585619168785393979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31809556780825558380525305 23857167585619168785393979)
        ·
          refine ⟨35785751378428753178090969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23857167585619168785393979 35785751378428753178090969)
          ·
            refine ⟨26839313533821564883568227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35785751378428753178090969 26839313533821564883568227)
            ·
              refine ⟨40258970300732347325352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26839313533821564883568227 40258970300732347325352341)
              ·
                refine ⟨1887139232846828780875891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40258970300732347325352341 1887139232846828780875891)
                ·
                  refine ⟨2830708849270243171313837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887139232846828780875891 2830708849270243171313837)
                  ·
                    refine ⟨1061515818476341189242689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830708849270243171313837 1061515818476341189242689)
                    ·
                      rfl

theorem cell22_3100942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3100942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3100942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3100942 prefixEnd_3100942 := by exact prefixLift 3100942
  have htrace : WordTrace (prefixWord ++ tailWord_3100942) baseStart_3100942 baseEnd_3100942 := by
    simpa [prefixWord, tailWord_3100942, baseEnd_3100942] using wordTrace_append hprefix tailTrace_3100942
  have hstable : (prefixWord ++ tailWord_3100942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3100942).length < 2 ^ (prefixWord ++ tailWord_3100942).sum := by decide
  have hdescent : baseEnd_3100942 < baseStart_3100942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3100942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101000 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_3101000 : Nat := 118140960795 + 3101000 * 2 ^ 59
def prefixEnd_3101000 : Nat := 4983230072969 + 3 ^ 40 * 3101000 * 2
def baseEnd_3101000 : Nat := 353845224353882790430837

theorem tailTrace_3101000 : CollatzResearch.WordTrace tailWord_3101000 prefixEnd_3101000 353845224353882790430837 := by
  unfold tailWord_3101000
  simp only [CollatzResearch.WordTrace]
  refine ⟨56551380882807041740406227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75401841177076055653874969 56551380882807041740406227)
  ·
    refine ⟨84827071324210562610609341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56551380882807041740406227 84827071324210562610609341)
    ·
      refine ⟨31810151746578960978978503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84827071324210562610609341 31810151746578960978978503)
      ·
        refine ⟨47715227619868441468467755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31810151746578960978978503 47715227619868441468467755)
        ·
          refine ⟨71572841429802662202701633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47715227619868441468467755 71572841429802662202701633)
          ·
            refine ⟨53679631072351996652026225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71572841429802662202701633 53679631072351996652026225)
            ·
              refine ⟨40259723304263997489019669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53679631072351996652026225 40259723304263997489019669)
              ·
                refine ⟨1887174529887374882297797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40259723304263997489019669 1887174529887374882297797)
                ·
                  refine ⟨353845224353882790430837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887174529887374882297797 353845224353882790430837)
                  ·
                    rfl

theorem cell22_3101000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_3101000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101000 prefixEnd_3101000 := by exact prefixLift 3101000
  have htrace : WordTrace (prefixWord ++ tailWord_3101000) baseStart_3101000 baseEnd_3101000 := by
    simpa [prefixWord, tailWord_3101000, baseEnd_3101000] using wordTrace_append hprefix tailTrace_3101000
  have hstable : (prefixWord ++ tailWord_3101000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101000).length < 2 ^ (prefixWord ++ tailWord_3101000).sum := by decide
  have hdescent : baseEnd_3101000 < baseStart_3101000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101028 : List Nat := [2, 3, 1, 1, 3, 1, 1, 10]
def baseStart_3101028 : Nat := 118140960795 + 3101028 * 2 ^ 59
def prefixEnd_3101028 : Nat := 4983230072969 + 3 ^ 40 * 3101028 * 2
def baseEnd_3101028 : Nat := 117949473114873959065825

theorem tailTrace_3101028 : CollatzResearch.WordTrace tailWord_3101028 prefixEnd_3101028 117949473114873959065825 := by
  unfold tailWord_3101028
  simp only [CollatzResearch.WordTrace]
  refine ⟨56551891504756322131415869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75402522006341762841887825 56551891504756322131415869)
  ·
    refine ⟨21206959314283620799280951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56551891504756322131415869 21206959314283620799280951)
    ·
      refine ⟨31810438971425431198921427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21206959314283620799280951 31810438971425431198921427)
      ·
        refine ⟨47715658457138146798382141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31810438971425431198921427 47715658457138146798382141)
        ·
          refine ⟨17893371921426805049393303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47715658457138146798382141 17893371921426805049393303)
          ·
            refine ⟨26840057882140207574089955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17893371921426805049393303 26840057882140207574089955)
            ·
              refine ⟨40260086823210311361134933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26840057882140207574089955 40260086823210311361134933)
              ·
                refine ⟨117949473114873959065825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40260086823210311361134933 117949473114873959065825)
                ·
                  rfl

theorem cell22_3101028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_3101028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101028 prefixEnd_3101028 := by exact prefixLift 3101028
  have htrace : WordTrace (prefixWord ++ tailWord_3101028) baseStart_3101028 baseEnd_3101028 := by
    simpa [prefixWord, tailWord_3101028, baseEnd_3101028] using wordTrace_append hprefix tailTrace_3101028
  have hstable : (prefixWord ++ tailWord_3101028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101028).length < 2 ^ (prefixWord ++ tailWord_3101028).sum := by decide
  have hdescent : baseEnd_3101028 < baseStart_3101028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101090 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_3101090 : Nat := 118140960795 + 3101090 * 2 ^ 59
def prefixEnd_3101090 : Nat := 4983230072969 + 3 ^ 40 * 3101090 * 2
def baseEnd_3101090 : Nat := 353855493966972712180745

theorem tailTrace_3101090 : CollatzResearch.WordTrace tailWord_3101090 prefixEnd_3101090 353855493966972712180745 := by
  unfold tailWord_3101090
  simp only [CollatzResearch.WordTrace]
  refine ⟨28276511083822007212897181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75404029556858685901059149 28276511083822007212897181)
  ·
    refine ⟨10603691656433252704836443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28276511083822007212897181 10603691656433252704836443)
    ·
      refine ⟨15905537484649879057254665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10603691656433252704836443 15905537484649879057254665)
      ·
        refine ⟨11929153113487409292940999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15905537484649879057254665 11929153113487409292940999)
        ·
          refine ⟨17893729670231113939411499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929153113487409292940999 17893729670231113939411499)
          ·
            refine ⟨26840594505346670909117249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17893729670231113939411499 26840594505346670909117249)
            ·
              refine ⟨20130445879010003181837937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26840594505346670909117249 20130445879010003181837937)
              ·
                refine ⟨15097834409257502386378453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20130445879010003181837937 15097834409257502386378453)
                ·
                  refine ⟨353855493966972712180745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15097834409257502386378453 353855493966972712180745)
                  ·
                    rfl

theorem cell22_3101090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_3101090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101090 prefixEnd_3101090 := by exact prefixLift 3101090
  have htrace : WordTrace (prefixWord ++ tailWord_3101090) baseStart_3101090 baseEnd_3101090 := by
    simpa [prefixWord, tailWord_3101090, baseEnd_3101090] using wordTrace_append hprefix tailTrace_3101090
  have hstable : (prefixWord ++ tailWord_3101090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101090).length < 2 ^ (prefixWord ++ tailWord_3101090).sum := by decide
  have hdescent : baseEnd_3101090 < baseStart_3101090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101105 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3101105 : Nat := 118140960795 + 3101105 * 2 ^ 59
def prefixEnd_3101105 : Nat := 4983230072969 + 3 ^ 40 * 3101105 * 2
def baseEnd_3101105 : Nat := 1061571616707463097417189

theorem tailTrace_3101105 : CollatzResearch.WordTrace tailWord_3101105 prefixEnd_3101105 1061571616707463097417189 := by
  unfold tailWord_3101105
  simp only [CollatzResearch.WordTrace]
  refine ⟨113106591430233686413384769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75404394286822457608923179 113106591430233686413384769)
  ·
    refine ⟨84829943572675264810038577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113106591430233686413384769 84829943572675264810038577)
    ·
      refine ⟨63622457679506448607528933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84829943572675264810038577 63622457679506448607528933)
      ·
        refine ⟨11929210814907459113911675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63622457679506448607528933 11929210814907459113911675)
        ·
          refine ⟨17893816222361188670867513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929210814907459113911675 17893816222361188670867513)
          ·
            refine ⟨13420362166770891503150635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17893816222361188670867513 13420362166770891503150635)
            ·
              refine ⟨20130543250156337254725953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13420362166770891503150635 20130543250156337254725953)
              ·
                refine ⟨15097907437617252941044465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20130543250156337254725953 15097907437617252941044465)
                ·
                  refine ⟨11323430578212939705783349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15097907437617252941044465 11323430578212939705783349)
                  ·
                    refine ⟨1061571616707463097417189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11323430578212939705783349 1061571616707463097417189)
                    ·
                      rfl

theorem cell22_3101105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3101105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101105 prefixEnd_3101105 := by exact prefixLift 3101105
  have htrace : WordTrace (prefixWord ++ tailWord_3101105) baseStart_3101105 baseEnd_3101105 := by
    simpa [prefixWord, tailWord_3101105, baseEnd_3101105] using wordTrace_append hprefix tailTrace_3101105
  have hstable : (prefixWord ++ tailWord_3101105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101105).length < 2 ^ (prefixWord ++ tailWord_3101105).sum := by decide
  have hdescent : baseEnd_3101105 < baseStart_3101105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101167 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 2, 3]
def baseStart_3101167 : Nat := 118140960795 + 3101167 * 2 ^ 59
def prefixEnd_3101167 : Nat := 4983230072969 + 3 ^ 40 * 3101167 * 2
def baseEnd_3101167 : Nat := 1061592840574515602366999

theorem tailTrace_3101167 : CollatzResearch.WordTrace tailWord_3101167 prefixEnd_3101167 1061592840574515602366999 := by
  unfold tailWord_3101167
  simp only [CollatzResearch.WordTrace]
  refine ⟨113108852756009071002141755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75405901837339380668094503 113108852756009071002141755)
  ·
    refine ⟨169663279134013606503212633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113108852756009071002141755 169663279134013606503212633)
    ·
      refine ⟨127247459350510204877409475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169663279134013606503212633 127247459350510204877409475)
      ·
        refine ⟨190871189025765307316114213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127247459350510204877409475 190871189025765307316114213)
        ·
          refine ⟨35788347942330995121771415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190871189025765307316114213 35788347942330995121771415)
          ·
            refine ⟨53682521913496492682657123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35788347942330995121771415 53682521913496492682657123)
            ·
              refine ⟨80523782870244739023985685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53682521913496492682657123 80523782870244739023985685)
              ·
                refine ⟨3774552322042722141749329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80523782870244739023985685 3774552322042722141749329)
                ·
                  refine ⟨2830914241532041606311997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3774552322042722141749329 2830914241532041606311997)
                  ·
                    refine ⟨1061592840574515602366999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2830914241532041606311997 1061592840574515602366999)
                    ·
                      rfl

theorem cell22_3101167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_3101167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101167 prefixEnd_3101167 := by exact prefixLift 3101167
  have htrace : WordTrace (prefixWord ++ tailWord_3101167) baseStart_3101167 baseEnd_3101167 := by
    simpa [prefixWord, tailWord_3101167, baseEnd_3101167] using wordTrace_append hprefix tailTrace_3101167
  have hstable : (prefixWord ++ tailWord_3101167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101167).length < 2 ^ (prefixWord ++ tailWord_3101167).sum := by decide
  have hdescent : baseEnd_3101167 < baseStart_3101167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101169 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 4]
def baseStart_3101169 : Nat := 118140960795 + 3101169 * 2 ^ 59
def prefixEnd_3101169 : Nat := 4983230072969 + 3 ^ 40 * 3101169 * 2
def baseEnd_3101169 : Nat := 353864508405129421272331

theorem tailTrace_3101169 : CollatzResearch.WordTrace tailWord_3101169 prefixEnd_3101169 353864508405129421272331 := by
  unfold tailWord_3101169
  simp only [CollatzResearch.WordTrace]
  refine ⟨113108925702001825343714561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75405950468001216895809707 113108925702001825343714561)
  ·
    refine ⟨84831694276501369007785921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113108925702001825343714561 84831694276501369007785921)
    ·
      refine ⟨63623770707376026755839441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84831694276501369007785921 63623770707376026755839441)
      ·
        refine ⟨47717828030532020066879581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63623770707376026755839441 47717828030532020066879581)
        ·
          refine ⟨17894185511449507525079843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47717828030532020066879581 17894185511449507525079843)
          ·
            refine ⟨26841278267174261287619765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17894185511449507525079843 26841278267174261287619765)
            ·
              refine ⟨2516369837547586995714353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26841278267174261287619765 2516369837547586995714353)
              ·
                refine ⟨1887277378160690246785765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516369837547586995714353 1887277378160690246785765)
                ·
                  refine ⟨353864508405129421272331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887277378160690246785765 353864508405129421272331)
                  ·
                    rfl

theorem cell22_3101169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_3101169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101169 prefixEnd_3101169 := by exact prefixLift 3101169
  have htrace : WordTrace (prefixWord ++ tailWord_3101169) baseStart_3101169 baseEnd_3101169 := by
    simpa [prefixWord, tailWord_3101169, baseEnd_3101169] using wordTrace_append hprefix tailTrace_3101169
  have hstable : (prefixWord ++ tailWord_3101169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101169).length < 2 ^ (prefixWord ++ tailWord_3101169).sum := by decide
  have hdescent : baseEnd_3101169 < baseStart_3101169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101220 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3101220 : Nat := 118140960795 + 3101220 * 2 ^ 59
def prefixEnd_3101220 : Nat := 4983230072969 + 3 ^ 40 * 3101220 * 2
def baseEnd_3101220 : Nat := 353870327852547043597279

theorem tailTrace_3101220 : CollatzResearch.WordTrace tailWord_3101220 prefixEnd_3101220 353870327852547043597279 := by
  unfold tailWord_3101220
  simp only [CollatzResearch.WordTrace]
  refine ⟨56555392912408530526910557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75407190549878040702547409 56555392912408530526910557)
  ·
    refine ⟨21208272342153198947591459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56555392912408530526910557 21208272342153198947591459)
    ·
      refine ⟨31812408513229798421387189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21208272342153198947591459 31812408513229798421387189)
      ·
        refine ⟨2982413298115293602005049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31812408513229798421387189 2982413298115293602005049)
        ·
          refine ⟨2236809973586470201503787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982413298115293602005049 2236809973586470201503787)
          ·
            refine ⟨3355214960379705302255681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236809973586470201503787 3355214960379705302255681)
            ·
              refine ⟨2516411220284778976691761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3355214960379705302255681 2516411220284778976691761)
              ·
                refine ⟨1887308415213584232518821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516411220284778976691761 1887308415213584232518821)
                ·
                  refine ⟨353870327852547043597279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887308415213584232518821 353870327852547043597279)
                  ·
                    rfl

theorem cell22_3101220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3101220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101220 prefixEnd_3101220 := by exact prefixLift 3101220
  have htrace : WordTrace (prefixWord ++ tailWord_3101220) baseStart_3101220 baseEnd_3101220 := by
    simpa [prefixWord, tailWord_3101220, baseEnd_3101220] using wordTrace_append hprefix tailTrace_3101220
  have hstable : (prefixWord ++ tailWord_3101220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101220).length < 2 ^ (prefixWord ++ tailWord_3101220).sum := by decide
  have hdescent : baseEnd_3101220 < baseStart_3101220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101242 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_3101242 : Nat := 118140960795 + 3101242 * 2 ^ 59
def prefixEnd_3101242 : Nat := 4983230072969 + 3 ^ 40 * 3101242 * 2
def baseEnd_3101242 : Nat := 353872838202413468913923

theorem tailTrace_3101242 : CollatzResearch.WordTrace tailWord_3101242 prefixEnd_3101242 353872838202413468913923 := by
  unfold tailWord_3101242
  simp only [CollatzResearch.WordTrace]
  refine ⟨28277897057684339702780495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75407725487158239207414653 28277897057684339702780495)
  ·
    refine ⟨42416845586526509554170743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28277897057684339702780495 42416845586526509554170743)
    ·
      refine ⟨63625268379789764331256115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42416845586526509554170743 63625268379789764331256115)
      ·
        refine ⟨95437902569684646496884173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63625268379789764331256115 95437902569684646496884173)
        ·
          refine ⟨35789213463631742436331565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95437902569684646496884173 35789213463631742436331565)
          ·
            refine ⟨13420955048861903413624337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35789213463631742436331565 13420955048861903413624337)
            ·
              refine ⟨10065716286646427560218253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13420955048861903413624337 10065716286646427560218253)
              ·
                refine ⟨3774643607492410335081845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10065716286646427560218253 3774643607492410335081845)
                ·
                  refine ⟨353872838202413468913923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3774643607492410335081845 353872838202413468913923)
                  ·
                    rfl

theorem cell22_3101242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_3101242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101242 prefixEnd_3101242 := by exact prefixLift 3101242
  have htrace : WordTrace (prefixWord ++ tailWord_3101242) baseStart_3101242 baseEnd_3101242 := by
    simpa [prefixWord, tailWord_3101242, baseEnd_3101242] using wordTrace_append hprefix tailTrace_3101242
  have hstable : (prefixWord ++ tailWord_3101242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101242).length < 2 ^ (prefixWord ++ tailWord_3101242).sum := by decide
  have hdescent : baseEnd_3101242 < baseStart_3101242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101276 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_3101276 : Nat := 118140960795 + 3101276 * 2 ^ 59
def prefixEnd_3101276 : Nat := 4983230072969 + 3 ^ 40 * 3101276 * 2
def baseEnd_3101276 : Nat := 353876717834025217130555

theorem tailTrace_3101276 : CollatzResearch.WordTrace tailWord_3101276 prefixEnd_3101276 353876717834025217130555 := by
  unfold tailWord_3101276
  simp only [CollatzResearch.WordTrace]
  refine ⟨56556414156307091308929841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75408552208409455078573121 56556414156307091308929841)
  ·
    refine ⟨42417310617230318481697381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56556414156307091308929841 42417310617230318481697381)
    ·
      refine ⟨7953245740730684715318259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42417310617230318481697381 7953245740730684715318259)
      ·
        refine ⟨11929868611096027072977389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953245740730684715318259 11929868611096027072977389)
        ·
          refine ⟨4473700729161010152366521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11929868611096027072977389 4473700729161010152366521)
          ·
            refine ⟨3355275546870757614274891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4473700729161010152366521 3355275546870757614274891)
            ·
              refine ⟨5032913320306136421412337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355275546870757614274891 5032913320306136421412337)
              ·
                refine ⟨3774684990229602316059253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5032913320306136421412337 3774684990229602316059253)
                ·
                  refine ⟨353876717834025217130555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3774684990229602316059253 353876717834025217130555)
                  ·
                    rfl

theorem cell22_3101276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_3101276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101276 prefixEnd_3101276 := by exact prefixLift 3101276
  have htrace : WordTrace (prefixWord ++ tailWord_3101276) baseStart_3101276 baseEnd_3101276 := by
    simpa [prefixWord, tailWord_3101276, baseEnd_3101276] using wordTrace_append hprefix tailTrace_3101276
  have hstable : (prefixWord ++ tailWord_3101276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101276).length < 2 ^ (prefixWord ++ tailWord_3101276).sum := by decide
  have hdescent : baseEnd_3101276 < baseStart_3101276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101314 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3101314 : Nat := 118140960795 + 3101314 * 2 ^ 59
def prefixEnd_3101314 : Nat := 4983230072969 + 3 ^ 40 * 3101314 * 2
def baseEnd_3101314 : Nat := 1061643161678656218941549

theorem tailTrace_3101314 : CollatzResearch.WordTrace tailWord_3101314 prefixEnd_3101314 1061643161678656218941549 := by
  unfold tailWord_3101314
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278553571619128776935749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75409476190984343405161997 28278553571619128776935749)
  ·
    refine ⟨5302228794678586645675453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28278553571619128776935749 5302228794678586645675453)
    ·
      refine ⟨1988335798004469992128295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5302228794678586645675453 1988335798004469992128295)
      ·
        refine ⟨2982503697006704988192443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988335798004469992128295 2982503697006704988192443)
        ·
          refine ⟨4473755545510057482288665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982503697006704988192443 4473755545510057482288665)
          ·
            refine ⟨3355316659132543111716499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4473755545510057482288665 3355316659132543111716499)
            ·
              refine ⟨5032974988698814667574749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355316659132543111716499 5032974988698814667574749)
              ·
                refine ⟨1887365620762055500340531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5032974988698814667574749 1887365620762055500340531)
                ·
                  refine ⟨2831048431143083250510797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887365620762055500340531 2831048431143083250510797)
                  ·
                    refine ⟨1061643161678656218941549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2831048431143083250510797 1061643161678656218941549)
                    ·
                      rfl

theorem cell22_3101314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3101314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101314 prefixEnd_3101314 := by exact prefixLift 3101314
  have htrace : WordTrace (prefixWord ++ tailWord_3101314) baseStart_3101314 baseEnd_3101314 := by
    simpa [prefixWord, tailWord_3101314, baseEnd_3101314] using wordTrace_append hprefix tailTrace_3101314
  have hstable : (prefixWord ++ tailWord_3101314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101314).length < 2 ^ (prefixWord ++ tailWord_3101314).sum := by decide
  have hdescent : baseEnd_3101314 < baseStart_3101314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101317 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_3101317 : Nat := 118140960795 + 3101317 * 2 ^ 59
def prefixEnd_3101317 : Nat := 4983230072969 + 3 ^ 40 * 3101317 * 2
def baseEnd_3101317 : Nat := 1061644188639965211116539

theorem tailTrace_3101317 : CollatzResearch.WordTrace tailWord_3101317 prefixEnd_3101317 1061644188639965211116539 := by
  unfold tailWord_3101317
  simp only [CollatzResearch.WordTrace]
  refine ⟨113114323705465646620102205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75409549136977097746734803 113114323705465646620102205)
  ·
    refine ⟨42417871389549617482538327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113114323705465646620102205 42417871389549617482538327)
    ·
      refine ⟨63626807084324426223807491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42417871389549617482538327 63626807084324426223807491)
      ·
        refine ⟨95440210626486639335711237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63626807084324426223807491 95440210626486639335711237)
        ·
          refine ⟨17895039492466244875445857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95440210626486639335711237 17895039492466244875445857)
          ·
            refine ⟨13421279619349683656584393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17895039492466244875445857 13421279619349683656584393)
            ·
              refine ⟨10065959714512262742438295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13421279619349683656584393 10065959714512262742438295)
              ·
                refine ⟨15098939571768394113657443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10065959714512262742438295 15098939571768394113657443)
                ·
                  refine ⟨22648409357652591170486165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15098939571768394113657443 22648409357652591170486165)
                  ·
                    refine ⟨1061644188639965211116539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22648409357652591170486165 1061644188639965211116539)
                    ·
                      rfl

theorem cell22_3101317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_3101317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101317 prefixEnd_3101317 := by exact prefixLift 3101317
  have htrace : WordTrace (prefixWord ++ tailWord_3101317) baseStart_3101317 baseEnd_3101317 := by
    simpa [prefixWord, tailWord_3101317, baseEnd_3101317] using wordTrace_append hprefix tailTrace_3101317
  have hstable : (prefixWord ++ tailWord_3101317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101317).length < 2 ^ (prefixWord ++ tailWord_3101317).sum := by decide
  have hdescent : baseEnd_3101317 < baseStart_3101317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101338 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_3101338 : Nat := 118140960795 + 3101338 * 2 ^ 59
def prefixEnd_3101338 : Nat := 4983230072969 + 3 ^ 40 * 3101338 * 2
def baseEnd_3101338 : Nat := 353883792456376052113825

theorem tailTrace_3101338 : CollatzResearch.WordTrace tailWord_3101338 prefixEnd_3101338 353883792456376052113825 := by
  unfold tailWord_3101338
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278772409597391801654167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75410059758926378137744445 28278772409597391801654167)
  ·
    refine ⟨42418158614396087702481251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28278772409597391801654167 42418158614396087702481251)
    ·
      refine ⟨63627237921594131553721877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42418158614396087702481251 63627237921594131553721877)
      ·
        refine ⟨2982526777574724916580713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63627237921594131553721877 2982526777574724916580713)
        ·
          refine ⟨2236895083181043687435535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982526777574724916580713 2236895083181043687435535)
          ·
            refine ⟨3355342624771565531153303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236895083181043687435535 3355342624771565531153303)
            ·
              refine ⟨5033013937157348296729955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355342624771565531153303 5033013937157348296729955)
              ·
                refine ⟨7549520905736022445094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033013937157348296729955 7549520905736022445094933)
                ·
                  refine ⟨353883792456376052113825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7549520905736022445094933 353883792456376052113825)
                  ·
                    rfl

theorem cell22_3101338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_3101338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101338 prefixEnd_3101338 := by exact prefixLift 3101338
  have htrace : WordTrace (prefixWord ++ tailWord_3101338) baseStart_3101338 baseEnd_3101338 := by
    simpa [prefixWord, tailWord_3101338, baseEnd_3101338] using wordTrace_append hprefix tailTrace_3101338
  have hstable : (prefixWord ++ tailWord_3101338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101338).length < 2 ^ (prefixWord ++ tailWord_3101338).sum := by decide
  have hdescent : baseEnd_3101338 < baseStart_3101338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101409 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3101409 : Nat := 118140960795 + 3101409 * 2 ^ 59
def prefixEnd_3101409 : Nat := 4983230072969 + 3 ^ 40 * 3101409 * 2
def baseEnd_3101409 : Nat := 1061675682120107637816257

theorem tailTrace_3101409 : CollatzResearch.WordTrace tailWord_3101409 prefixEnd_3101409 1061675682120107637816257 := by
  unfold tailWord_3101409
  simp only [CollatzResearch.WordTrace]
  refine ⟨113117679221132346332451281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75411786147421564221634187 113117679221132346332451281)
  ·
    refine ⟨84838259415849259749338461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113117679221132346332451281 84838259415849259749338461)
    ·
      refine ⟨31814347280943472406001923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84838259415849259749338461 31814347280943472406001923)
      ·
        refine ⟨47721520921415208609002885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31814347280943472406001923 47721520921415208609002885)
        ·
          refine ⟨8947785172765351614188041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47721520921415208609002885 8947785172765351614188041)
          ·
            refine ⟨6710838879574013710641031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8947785172765351614188041 6710838879574013710641031)
            ·
              refine ⟨10066258319361020565961547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6710838879574013710641031 10066258319361020565961547)
              ·
                refine ⟨15099387479041530848942321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10066258319361020565961547 15099387479041530848942321)
                ·
                  refine ⟨11324540609281148136706741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15099387479041530848942321 11324540609281148136706741)
                  ·
                    refine ⟨1061675682120107637816257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11324540609281148136706741 1061675682120107637816257)
                    ·
                      rfl

theorem cell22_3101409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3101409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101409 prefixEnd_3101409 := by exact prefixLift 3101409
  have htrace : WordTrace (prefixWord ++ tailWord_3101409) baseStart_3101409 baseEnd_3101409 := by
    simpa [prefixWord, tailWord_3101409, baseEnd_3101409] using wordTrace_append hprefix tailTrace_3101409
  have hstable : (prefixWord ++ tailWord_3101409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101409).length < 2 ^ (prefixWord ++ tailWord_3101409).sum := by decide
  have hdescent : baseEnd_3101409 < baseStart_3101409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101424 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_3101424 : Nat := 118140960795 + 3101424 * 2 ^ 59
def prefixEnd_3101424 : Nat := 4983230072969 + 3 ^ 40 * 3101424 * 2
def baseEnd_3101424 : Nat := 1061680816926652598691211

theorem tailTrace_3101424 : CollatzResearch.WordTrace tailWord_3101424 prefixEnd_3101424 1061680816926652598691211 := by
  unfold tailWord_3101424
  simp only [CollatzResearch.WordTrace]
  refine ⟨56559113158039001947123663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75412150877385335929498217 56559113158039001947123663)
  ·
    refine ⟨84838669737058502920685495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56559113158039001947123663 84838669737058502920685495)
    ·
      refine ⟨127258004605587754381028243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84838669737058502920685495 127258004605587754381028243)
      ·
        refine ⟨190887006908381631571542365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127258004605587754381028243 190887006908381631571542365)
        ·
          refine ⟨71582627590643111839328387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190887006908381631571542365 71582627590643111839328387)
          ·
            refine ⟨107373941385964667758992581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71582627590643111839328387 107373941385964667758992581)
            ·
              refine ⟨20132614009868375204811109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107373941385964667758992581 20132614009868375204811109)
              ·
                refine ⟨3774865126850320350902083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20132614009868375204811109 3774865126850320350902083)
                ·
                  refine ⟨5662297690275480526353125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774865126850320350902083 5662297690275480526353125)
                  ·
                    refine ⟨1061680816926652598691211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5662297690275480526353125 1061680816926652598691211)
                    ·
                      rfl

theorem cell22_3101424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_3101424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101424 prefixEnd_3101424 := by exact prefixLift 3101424
  have htrace : WordTrace (prefixWord ++ tailWord_3101424) baseStart_3101424 baseEnd_3101424 := by
    simpa [prefixWord, tailWord_3101424, baseEnd_3101424] using wordTrace_append hprefix tailTrace_3101424
  have hstable : (prefixWord ++ tailWord_3101424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101424).length < 2 ^ (prefixWord ++ tailWord_3101424).sum := by decide
  have hdescent : baseEnd_3101424 < baseStart_3101424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101471 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 1, 5]
def baseStart_3101471 : Nat := 118140960795 + 3101471 * 2 ^ 59
def prefixEnd_3101471 : Nat := 4983230072969 + 3 ^ 40 * 3101471 * 2
def baseEnd_3101471 : Nat := 1061696905987160142766067

theorem tailTrace_3101471 : CollatzResearch.WordTrace tailWord_3101471 prefixEnd_3101471 1061696905987160142766067 := by
  unfold tailWord_3101471
  simp only [CollatzResearch.WordTrace]
  refine ⟨113119940546907730921208267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75413293697938487280805511 113119940546907730921208267)
  ·
    refine ⟨169679910820361596381812401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113119940546907730921208267 169679910820361596381812401)
    ·
      refine ⟨127259933115271197286359301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169679910820361596381812401 127259933115271197286359301)
      ·
        refine ⟨23861237459113349491192369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127259933115271197286359301 23861237459113349491192369)
        ·
          refine ⟨17895928094335012118394277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23861237459113349491192369 17895928094335012118394277)
          ·
            refine ⟨3355486517687814772198927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17895928094335012118394277 3355486517687814772198927)
            ·
              refine ⟨5033229776531722158298391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355486517687814772198927 5033229776531722158298391)
              ·
                refine ⟨7549844664797583237447587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033229776531722158298391 7549844664797583237447587)
                ·
                  refine ⟨11324766997196374856171381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7549844664797583237447587 11324766997196374856171381)
                  ·
                    refine ⟨1061696905987160142766067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11324766997196374856171381 1061696905987160142766067)
                    ·
                      rfl

theorem cell22_3101471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_3101471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101471 prefixEnd_3101471 := by exact prefixLift 3101471
  have htrace : WordTrace (prefixWord ++ tailWord_3101471) baseStart_3101471 baseEnd_3101471 := by
    simpa [prefixWord, tailWord_3101471, baseEnd_3101471] using wordTrace_append hprefix tailTrace_3101471
  have hstable : (prefixWord ++ tailWord_3101471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101471).length < 2 ^ (prefixWord ++ tailWord_3101471).sum := by decide
  have hdescent : baseEnd_3101471 < baseStart_3101471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101486 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3101486 : Nat := 118140960795 + 3101486 * 2 ^ 59
def prefixEnd_3101486 : Nat := 4983230072969 + 3 ^ 40 * 3101486 * 2
def baseEnd_3101486 : Nat := 1061702040793705103641021

theorem tailTrace_3101486 : CollatzResearch.WordTrace tailWord_3101486 prefixEnd_3101486 1061702040793705103641021 := by
  unfold tailWord_3101486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14140060955231673560375539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75413658427902258988669541 14140060955231673560375539)
  ·
    refine ⟨21210091432847510340563309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14140060955231673560375539 21210091432847510340563309)
    ·
      refine ⟨7953784287317816377711241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21210091432847510340563309 7953784287317816377711241)
      ·
        refine ⟨5965338215488362283283431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7953784287317816377711241 5965338215488362283283431)
        ·
          refine ⟨8948007323232543424925147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965338215488362283283431 8948007323232543424925147)
          ·
            refine ⟨13422010984848815137387721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948007323232543424925147 13422010984848815137387721)
            ·
              refine ⟨10066508238636611353040791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13422010984848815137387721 10066508238636611353040791)
              ·
                refine ⟨15099762357954917029561187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10066508238636611353040791 15099762357954917029561187)
                ·
                  refine ⟨22649643536932375544341781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15099762357954917029561187 22649643536932375544341781)
                  ·
                    refine ⟨1061702040793705103641021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22649643536932375544341781 1061702040793705103641021)
                    ·
                      rfl

theorem cell22_3101486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3101486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101486 prefixEnd_3101486 := by exact prefixLift 3101486
  have htrace : WordTrace (prefixWord ++ tailWord_3101486) baseStart_3101486 baseEnd_3101486 := by
    simpa [prefixWord, tailWord_3101486, baseEnd_3101486] using wordTrace_append hprefix tailTrace_3101486
  have hstable : (prefixWord ++ tailWord_3101486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101486).length < 2 ^ (prefixWord ++ tailWord_3101486).sum := by decide
  have hdescent : baseEnd_3101486 < baseStart_3101486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101501 : List Nat := [1, 4, 1, 4, 2, 2, 8]
def baseStart_3101501 : Nat := 118140960795 + 3101501 * 2 ^ 59
def prefixEnd_3101501 : Nat := 4983230072969 + 3 ^ 40 * 3101501 * 2
def baseEnd_3101501 : Nat := 39322487985194446833925

theorem tailTrace_3101501 : CollatzResearch.WordTrace tailWord_3101501 prefixEnd_3101501 39322487985194446833925 := by
  unfold tailWord_3101501
  simp only [CollatzResearch.WordTrace]
  refine ⟨113121034736799046044800357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75414023157866030696533571 113121034736799046044800357)
  ·
    refine ⟨21210194013149821133400067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113121034736799046044800357 21210194013149821133400067)
    ·
      refine ⟨31815291019724731700100101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21210194013149821133400067 31815291019724731700100101)
      ·
        refine ⟨5965367066198387193768769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31815291019724731700100101 5965367066198387193768769)
        ·
          refine ⟨4474025299648790395326577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5965367066198387193768769 4474025299648790395326577)
          ·
            refine ⟨3355518974736592796494933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474025299648790395326577 3355518974736592796494933)
            ·
              refine ⟨39322487985194446833925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3355518974736592796494933 39322487985194446833925)
              ·
                rfl

theorem cell22_3101501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 8].length) (baseStart_3101501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101501 prefixEnd_3101501 := by exact prefixLift 3101501
  have htrace : WordTrace (prefixWord ++ tailWord_3101501) baseStart_3101501 baseEnd_3101501 := by
    simpa [prefixWord, tailWord_3101501, baseEnd_3101501] using wordTrace_append hprefix tailTrace_3101501
  have hstable : (prefixWord ++ tailWord_3101501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101501).length < 2 ^ (prefixWord ++ tailWord_3101501).sum := by decide
  have hdescent : baseEnd_3101501 < baseStart_3101501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101576 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3101576 : Nat := 118140960795 + 3101576 * 2 ^ 59
def prefixEnd_3101576 : Nat := 4983230072969 + 3 ^ 40 * 3101576 * 2
def baseEnd_3101576 : Nat := 1061732849632974868890745

theorem tailTrace_3101576 : CollatzResearch.WordTrace tailWord_3101576 prefixEnd_3101576 1061732849632974868890745 := by
  unfold tailWord_3101576
  simp only [CollatzResearch.WordTrace]
  refine ⟨56561885105763666926890291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75415846807684889235853721 56561885105763666926890291)
  ·
    refine ⟨84842827658645500390335437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56561885105763666926890291 84842827658645500390335437)
    ·
      refine ⟨31816060371992062646375789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84842827658645500390335437 31816060371992062646375789)
      ·
        refine ⟨11931022639497023492390921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31816060371992062646375789 11931022639497023492390921)
        ·
          refine ⟨8948266979622767619293191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11931022639497023492390921 8948266979622767619293191)
          ·
            refine ⟨13422400469434151428939787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948266979622767619293191 13422400469434151428939787)
            ·
              refine ⟨20133600704151227143409681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13422400469434151428939787 20133600704151227143409681)
              ·
                refine ⟨15100200528113420357557261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20133600704151227143409681 15100200528113420357557261)
                ·
                  refine ⟨5662575198042532634083973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15100200528113420357557261 5662575198042532634083973)
                  ·
                    refine ⟨1061732849632974868890745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5662575198042532634083973 1061732849632974868890745)
                    ·
                      rfl

theorem cell22_3101576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3101576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101576 prefixEnd_3101576 := by exact prefixLift 3101576
  have htrace : WordTrace (prefixWord ++ tailWord_3101576) baseStart_3101576 baseEnd_3101576 := by
    simpa [prefixWord, tailWord_3101576, baseEnd_3101576] using wordTrace_append hprefix tailTrace_3101576
  have hstable : (prefixWord ++ tailWord_3101576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101576).length < 2 ^ (prefixWord ++ tailWord_3101576).sum := by decide
  have hdescent : baseEnd_3101576 < baseStart_3101576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101621 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3101621 : Nat := 118140960795 + 3101621 * 2 ^ 59
def prefixEnd_3101621 : Nat := 4983230072969 + 3 ^ 40 * 3101621 * 2
def baseEnd_3101621 : Nat := 1061748254052609751515607

theorem tailTrace_3101621 : CollatzResearch.WordTrace tailWord_3101621 prefixEnd_3101621 1061748254052609751515607 := by
  unfold tailWord_3101621
  simp only [CollatzResearch.WordTrace]
  refine ⟨113125411496364306539168717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75416940997576204359445811 113125411496364306539168717)
  ·
    refine ⟨42422029311136614952188269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113125411496364306539168717 42422029311136614952188269)
    ·
      refine ⟨15908260991676230607070601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42422029311136614952188269 15908260991676230607070601)
      ·
        refine ⟨11931195743757172955302951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15908260991676230607070601 11931195743757172955302951)
        ·
          refine ⟨17896793615635759432954427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11931195743757172955302951 17896793615635759432954427)
          ·
            refine ⟨26845190423453639149431641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17896793615635759432954427 26845190423453639149431641)
            ·
              refine ⟨20133892817590229362073731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26845190423453639149431641 20133892817590229362073731)
              ·
                refine ⟨30200839226385344043110597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20133892817590229362073731 30200839226385344043110597)
                ·
                  refine ⟨5662657354947252008083237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30200839226385344043110597 5662657354947252008083237)
                  ·
                    refine ⟨1061748254052609751515607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5662657354947252008083237 1061748254052609751515607)
                    ·
                      rfl

theorem cell22_3101621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3101621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101621 prefixEnd_3101621 := by exact prefixLift 3101621
  have htrace : WordTrace (prefixWord ++ tailWord_3101621) baseStart_3101621 baseEnd_3101621 := by
    simpa [prefixWord, tailWord_3101621, baseEnd_3101621] using wordTrace_append hprefix tailTrace_3101621
  have hstable : (prefixWord ++ tailWord_3101621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101621).length < 2 ^ (prefixWord ++ tailWord_3101621).sum := by decide
  have hdescent : baseEnd_3101621 < baseStart_3101621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101623 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 2, 3]
def baseStart_3101623 : Nat := 118140960795 + 3101623 * 2 ^ 59
def prefixEnd_3101623 : Nat := 4983230072969 + 3 ^ 40 * 3101623 * 2
def baseEnd_3101623 : Nat := 1061748938693482412965601

theorem tailTrace_3101623 : CollatzResearch.WordTrace tailWord_3101623 prefixEnd_3101623 1061748938693482412965601 := by
  unfold tailWord_3101623
  simp only [CollatzResearch.WordTrace]
  refine ⟨113125484442357060880741523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75416989628238040587161015 113125484442357060880741523)
  ·
    refine ⟨169688226663535591321112285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113125484442357060880741523 169688226663535591321112285)
    ·
      refine ⟨63633084998825846745417107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169688226663535591321112285 63633084998825846745417107)
      ·
        refine ⟨95449627498238770118125661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63633084998825846745417107 95449627498238770118125661)
        ·
          refine ⟨35793610311839538794297123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95449627498238770118125661 35793610311839538794297123)
          ·
            refine ⟨53690415467759308191445685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35793610311839538794297123 53690415467759308191445685)
            ·
              refine ⟨5033476450102435142948033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53690415467759308191445685 5033476450102435142948033)
              ·
                refine ⟨3775107337576826357211025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5033476450102435142948033 3775107337576826357211025)
                ·
                  refine ⟨2831330503182619767908269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3775107337576826357211025 2831330503182619767908269)
                  ·
                    refine ⟨1061748938693482412965601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2831330503182619767908269 1061748938693482412965601)
                    ·
                      rfl

theorem cell22_3101623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_3101623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101623 prefixEnd_3101623 := by exact prefixLift 3101623
  have htrace : WordTrace (prefixWord ++ tailWord_3101623) baseStart_3101623 baseEnd_3101623 := by
    simpa [prefixWord, tailWord_3101623, baseEnd_3101623] using wordTrace_append hprefix tailTrace_3101623
  have hstable : (prefixWord ++ tailWord_3101623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101623).length < 2 ^ (prefixWord ++ tailWord_3101623).sum := by decide
  have hdescent : baseEnd_3101623 < baseStart_3101623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101640 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 1, 5]
def baseStart_3101640 : Nat := 118140960795 + 3101640 * 2 ^ 59
def prefixEnd_3101640 : Nat := 4983230072969 + 3 ^ 40 * 3101640 * 2
def baseEnd_3101640 : Nat := 1061754758140900035290549

theorem tailTrace_3101640 : CollatzResearch.WordTrace tailWord_3101640 prefixEnd_3101640 1061754758140900035290549 := by
  unfold tailWord_3101640
  simp only [CollatzResearch.WordTrace]
  refine ⟨56563052241647736392055187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75417402988863648522740249 56563052241647736392055187)
  ·
    refine ⟨84844578362471604588082781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56563052241647736392055187 84844578362471604588082781)
    ·
      refine ⟨31816716885926851720531043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84844578362471604588082781 31816716885926851720531043)
      ·
        refine ⟨47725075328890277580796565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31816716885926851720531043 47725075328890277580796565)
        ·
          refine ⟨2237112906041731761599839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47725075328890277580796565 2237112906041731761599839)
          ·
            refine ⟨3355669359062597642399759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237112906041731761599839 3355669359062597642399759)
            ·
              refine ⟨5033504038593896463599639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355669359062597642399759 5033504038593896463599639)
              ·
                refine ⟨7550256057890844695399459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033504038593896463599639 7550256057890844695399459)
                ·
                  refine ⟨11325384086836267043099189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550256057890844695399459 11325384086836267043099189)
                  ·
                    refine ⟨1061754758140900035290549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11325384086836267043099189 1061754758140900035290549)
                    ·
                      rfl

theorem cell22_3101640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_3101640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101640 prefixEnd_3101640 := by exact prefixLift 3101640
  have htrace : WordTrace (prefixWord ++ tailWord_3101640) baseStart_3101640 baseEnd_3101640 := by
    simpa [prefixWord, tailWord_3101640, baseEnd_3101640] using wordTrace_append hprefix tailTrace_3101640
  have hstable : (prefixWord ++ tailWord_3101640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101640).length < 2 ^ (prefixWord ++ tailWord_3101640).sum := by decide
  have hdescent : baseEnd_3101640 < baseStart_3101640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101681 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 7]
def baseStart_3101681 : Nat := 118140960795 + 3101681 * 2 ^ 59
def prefixEnd_3101681 : Nat := 4983230072969 + 3 ^ 40 * 3101681 * 2
def baseEnd_3101681 : Nat := 353922931092929865005141

theorem tailTrace_3101681 : CollatzResearch.WordTrace tailWord_3101681 prefixEnd_3101681 353922931092929865005141 := by
  unfold tailWord_3101681
  simp only [CollatzResearch.WordTrace]
  refine ⟨113127599876146936786352897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75418399917431291190901931 113127599876146936786352897)
  ·
    refine ⟨84845699907110202589764673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113127599876146936786352897 84845699907110202589764673)
    ·
      refine ⟨63634274930332651942323505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84845699907110202589764673 63634274930332651942323505)
      ·
        refine ⟨47725706197749488956742629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63634274930332651942323505 47725706197749488956742629)
        ·
          refine ⟨8948569912078029179389243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47725706197749488956742629 8948569912078029179389243)
          ·
            refine ⟨13422854868117043769083865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948569912078029179389243 13422854868117043769083865)
            ·
              refine ⟨10067141151087782826812899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13422854868117043769083865 10067141151087782826812899)
              ·
                refine ⟨15100711726631674240219349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10067141151087782826812899 15100711726631674240219349)
                ·
                  refine ⟨353922931092929865005141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15100711726631674240219349 353922931092929865005141)
                  ·
                    rfl

theorem cell22_3101681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_3101681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101681 prefixEnd_3101681 := by exact prefixLift 3101681
  have htrace : WordTrace (prefixWord ++ tailWord_3101681) baseStart_3101681 baseEnd_3101681 := by
    simpa [prefixWord, tailWord_3101681, baseEnd_3101681] using wordTrace_append hprefix tailTrace_3101681
  have hstable : (prefixWord ++ tailWord_3101681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101681).length < 2 ^ (prefixWord ++ tailWord_3101681).sum := by decide
  have hdescent : baseEnd_3101681 < baseStart_3101681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101854 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3101854 : Nat := 118140960795 + 3101854 * 2 ^ 59
def prefixEnd_3101854 : Nat := 4983230072969 + 3 ^ 40 * 3101854 * 2
def baseEnd_3101854 : Nat := 1061828014714274810439893

theorem tailTrace_3101854 : CollatzResearch.WordTrace tailWord_3101854 prefixEnd_3101854 1061828014714274810439893 := by
  unfold tailWord_3101854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141738713065023416550077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75422606469680124888267077 14141738713065023416550077)
  ·
    refine ⟨5303152017399383781206279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14141738713065023416550077 5303152017399383781206279)
    ·
      refine ⟨7954728026099075671809419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5303152017399383781206279 7954728026099075671809419)
      ·
        refine ⟨11932092039148613507714129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7954728026099075671809419 11932092039148613507714129)
        ·
          refine ⟨8949069029361460130785597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11932092039148613507714129 8949069029361460130785597)
          ·
            refine ⟨3355900886010547549044599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8949069029361460130785597 3355900886010547549044599)
            ·
              refine ⟨5033851329015821323566899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355900886010547549044599 5033851329015821323566899)
              ·
                refine ⟨7550776993523731985350349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033851329015821323566899 7550776993523731985350349)
                ·
                  refine ⟨2831541372571399494506381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7550776993523731985350349 2831541372571399494506381)
                  ·
                    refine ⟨1061828014714274810439893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2831541372571399494506381 1061828014714274810439893)
                    ·
                      rfl

theorem cell22_3101854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3101854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101854 prefixEnd_3101854 := by exact prefixLift 3101854
  have htrace : WordTrace (prefixWord ++ tailWord_3101854) baseStart_3101854 baseEnd_3101854 := by
    simpa [prefixWord, tailWord_3101854, baseEnd_3101854] using wordTrace_append hprefix tailTrace_3101854
  have hstable : (prefixWord ++ tailWord_3101854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101854).length < 2 ^ (prefixWord ++ tailWord_3101854).sum := by decide
  have hdescent : baseEnd_3101854 < baseStart_3101854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101912 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_3101912 : Nat := 118140960795 + 3101912 * 2 ^ 59
def prefixEnd_3101912 : Nat := 4983230072969 + 3 ^ 40 * 3101912 * 2
def baseEnd_3101912 : Nat := 353949289766527330829905

theorem tailTrace_3101912 : CollatzResearch.WordTrace tailWord_3101912 prefixEnd_3101912 353949289766527330829905 := by
  unfold tailWord_3101912
  simp only [CollatzResearch.WordTrace]
  refine ⟨56568012569155031619005995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75424016758873375492007993 56568012569155031619005995)
  ·
    refine ⟨84852018853732547428508993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56568012569155031619005995 84852018853732547428508993)
    ·
      refine ⟨63639014140299410571381745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84852018853732547428508993 63639014140299410571381745)
      ·
        refine ⟨47729260605224557928536309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63639014140299410571381745 47729260605224557928536309)
        ·
          refine ⟨4474618181739802305800279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47729260605224557928536309 4474618181739802305800279)
          ·
            refine ⟨6711927272609703458700419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474618181739802305800279 6711927272609703458700419)
            ·
              refine ⟨10067890908914555188050629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6711927272609703458700419 10067890908914555188050629)
              ·
                refine ⟨1887729545421479097759493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10067890908914555188050629 1887729545421479097759493)
                ·
                  refine ⟨353949289766527330829905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1887729545421479097759493 353949289766527330829905)
                  ·
                    rfl

theorem cell22_3101912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_3101912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101912 prefixEnd_3101912 := by exact prefixLift 3101912
  have htrace : WordTrace (prefixWord ++ tailWord_3101912) baseStart_3101912 baseEnd_3101912 := by
    simpa [prefixWord, tailWord_3101912, baseEnd_3101912] using wordTrace_append hprefix tailTrace_3101912
  have hstable : (prefixWord ++ tailWord_3101912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101912).length < 2 ^ (prefixWord ++ tailWord_3101912).sum := by decide
  have hdescent : baseEnd_3101912 < baseStart_3101912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3101927 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3101927 : Nat := 118140960795 + 3101927 * 2 ^ 59
def prefixEnd_3101927 : Nat := 4983230072969 + 3 ^ 40 * 3101927 * 2
def baseEnd_3101927 : Nat := 1061853004106126953364669

theorem tailTrace_3101927 : CollatzResearch.WordTrace tailWord_3101927 prefixEnd_3101927 1061853004106126953364669 := by
  unfold tailWord_3101927
  simp only [CollatzResearch.WordTrace]
  refine ⟨113136572233255720799808035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75424381488837147199872023 113136572233255720799808035)
  ·
    refine ⟨169704858349883581199712053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113136572233255720799808035 169704858349883581199712053)
    ·
      refine ⟨15909830470301585737473005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169704858349883581199712053 15909830470301585737473005)
      ·
        refine ⟨5966186426363094651552377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15909830470301585737473005 5966186426363094651552377)
        ·
          refine ⟨4474639819772320988664283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5966186426363094651552377 4474639819772320988664283)
          ·
            refine ⟨6711959729658481482996425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474639819772320988664283 6711959729658481482996425)
            ·
              refine ⟨5033969797243861112247319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6711959729658481482996425 5033969797243861112247319)
              ·
                refine ⟨7550954695865791668370979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5033969797243861112247319 7550954695865791668370979)
                ·
                  refine ⟨11326432043798687502556469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550954695865791668370979 11326432043798687502556469)
                  ·
                    refine ⟨1061853004106126953364669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11326432043798687502556469 1061853004106126953364669)
                    ·
                      rfl

theorem cell22_3101927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3101927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3101927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3101927 prefixEnd_3101927 := by exact prefixLift 3101927
  have htrace : WordTrace (prefixWord ++ tailWord_3101927) baseStart_3101927 baseEnd_3101927 := by
    simpa [prefixWord, tailWord_3101927, baseEnd_3101927] using wordTrace_append hprefix tailTrace_3101927
  have hstable : (prefixWord ++ tailWord_3101927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3101927).length < 2 ^ (prefixWord ++ tailWord_3101927).sum := by decide
  have hdescent : baseEnd_3101927 < baseStart_3101927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3101927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102124 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_3102124 : Nat := 118140960795 + 3102124 * 2 ^ 59
def prefixEnd_3102124 : Nat := 4983230072969 + 3 ^ 40 * 3102124 * 2
def baseEnd_3102124 : Nat := 1061920441232084106189065

theorem tailTrace_3102124 : CollatzResearch.WordTrace tailWord_3102124 prefixEnd_3102124 1061920441232084106189065 := by
  unfold tailWord_3102124
  simp only [CollatzResearch.WordTrace]
  refine ⟨56571878706771011722364713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75429171609028015629819617 56571878706771011722364713)
  ·
    refine ⟨42428909030078258791773535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56571878706771011722364713 42428909030078258791773535)
    ·
      refine ⟨63643363545117388187660303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42428909030078258791773535 63643363545117388187660303)
      ·
        refine ⟨95465045317676082281490455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63643363545117388187660303 95465045317676082281490455)
        ·
          refine ⟨143197567976514123422235683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95465045317676082281490455 143197567976514123422235683)
          ·
            refine ⟨214796351964771185133353525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143197567976514123422235683 214796351964771185133353525)
            ·
              refine ⟨20137157996697298606251893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214796351964771185133353525 20137157996697298606251893)
              ·
                refine ⟨1887858562190371744336115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20137157996697298606251893 1887858562190371744336115)
                ·
                  refine ⟨2831787843285557616504173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887858562190371744336115 2831787843285557616504173)
                  ·
                    refine ⟨1061920441232084106189065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2831787843285557616504173 1061920441232084106189065)
                    ·
                      rfl

theorem cell22_3102124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_3102124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102124 prefixEnd_3102124 := by exact prefixLift 3102124
  have htrace : WordTrace (prefixWord ++ tailWord_3102124) baseStart_3102124 baseEnd_3102124 := by
    simpa [prefixWord, tailWord_3102124, baseEnd_3102124] using wordTrace_append hprefix tailTrace_3102124
  have hstable : (prefixWord ++ tailWord_3102124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102124).length < 2 ^ (prefixWord ++ tailWord_3102124).sum := by decide
  have hdescent : baseEnd_3102124 < baseStart_3102124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102135 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3102135 : Nat := 118140960795 + 3102135 * 2 ^ 59
def prefixEnd_3102135 : Nat := 4983230072969 + 3 ^ 40 * 3102135 * 2
def baseEnd_3102135 : Nat := 1061924206756883744164031

theorem tailTrace_3102135 : CollatzResearch.WordTrace tailWord_3102135 prefixEnd_3102135 1061924206756883744164031 := by
  unfold tailWord_3102135
  simp only [CollatzResearch.WordTrace]
  refine ⟨113144158616502172323379859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75429439077668114882253239 113144158616502172323379859)
  ·
    refine ⟨169716237924753258485069789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113144158616502172323379859 169716237924753258485069789)
    ·
      refine ⟨63643589221782471931901171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169716237924753258485069789 63643589221782471931901171)
      ·
        refine ⟨95465383832673707897851757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63643589221782471931901171 95465383832673707897851757)
        ·
          refine ⟨35799518937252640461694409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95465383832673707897851757 35799518937252640461694409)
          ·
            refine ⟨26849639202939480346270807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35799518937252640461694409 26849639202939480346270807)
            ·
              refine ⟨40274458804409220519406211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26849639202939480346270807 40274458804409220519406211)
              ·
                refine ⟨60411688206613830779109317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40274458804409220519406211 60411688206613830779109317)
                ·
                  refine ⟨11327191538740093271082997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60411688206613830779109317 11327191538740093271082997)
                  ·
                    refine ⟨1061924206756883744164031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11327191538740093271082997 1061924206756883744164031)
                    ·
                      rfl

theorem cell22_3102135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3102135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102135 prefixEnd_3102135 := by exact prefixLift 3102135
  have htrace : WordTrace (prefixWord ++ tailWord_3102135) baseStart_3102135 baseEnd_3102135 := by
    simpa [prefixWord, tailWord_3102135, baseEnd_3102135] using wordTrace_append hprefix tailTrace_3102135
  have hstable : (prefixWord ++ tailWord_3102135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102135).length < 2 ^ (prefixWord ++ tailWord_3102135).sum := by decide
  have hdescent : baseEnd_3102135 < baseStart_3102135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102137 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 7]
def baseStart_3102137 : Nat := 118140960795 + 3102137 * 2 ^ 59
def prefixEnd_3102137 : Nat := 4983230072969 + 3 ^ 40 * 3102137 * 2
def baseEnd_3102137 : Nat := 353974963799252135204675

theorem tailTrace_3102137 : CollatzResearch.WordTrace tailWord_3102137 prefixEnd_3102137 353974963799252135204675 := by
  unfold tailWord_3102137
  simp only [CollatzResearch.WordTrace]
  refine ⟨113144231562494926664952665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75429487708329951109968443 113144231562494926664952665)
  ·
    refine ⟨84858173671871194998714499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113144231562494926664952665 84858173671871194998714499)
    ·
      refine ⟨127287260507806792498071749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84858173671871194998714499 127287260507806792498071749)
      ·
        refine ⟨23866361345213773593388453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127287260507806792498071749 23866361345213773593388453)
        ·
          refine ⟨4474942752227582548760335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23866361345213773593388453 4474942752227582548760335)
          ·
            refine ⟨6712414128341373823140503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474942752227582548760335 6712414128341373823140503)
            ·
              refine ⟨10068621192512060734710755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712414128341373823140503 10068621192512060734710755)
              ·
                refine ⟨15102931788768091102066133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10068621192512060734710755 15102931788768091102066133)
                ·
                  refine ⟨353974963799252135204675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15102931788768091102066133 353974963799252135204675)
                  ·
                    rfl

theorem cell22_3102137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_3102137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102137 prefixEnd_3102137 := by exact prefixLift 3102137
  have htrace : WordTrace (prefixWord ++ tailWord_3102137) baseStart_3102137 baseEnd_3102137 := by
    simpa [prefixWord, tailWord_3102137, baseEnd_3102137] using wordTrace_append hprefix tailTrace_3102137
  have hstable : (prefixWord ++ tailWord_3102137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102137).length < 2 ^ (prefixWord ++ tailWord_3102137).sum := by decide
  have hdescent : baseEnd_3102137 < baseStart_3102137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102154 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_3102154 : Nat := 118140960795 + 3102154 * 2 ^ 59
def prefixEnd_3102154 : Nat := 4983230072969 + 3 ^ 40 * 3102154 * 2
def baseEnd_3102154 : Nat := 353976903615058009312991

theorem tailTrace_3102154 : CollatzResearch.WordTrace tailWord_3102154 prefixEnd_3102154 353976903615058009312991 := by
  unfold tailWord_3102154
  simp only [CollatzResearch.WordTrace]
  refine ⟨28286212900858334642080379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75429901068955559045547677 28286212900858334642080379)
  ·
    refine ⟨42429319351287501963120569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28286212900858334642080379 42429319351287501963120569)
    ·
      refine ⟨31821989513465626472340427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42429319351287501963120569 31821989513465626472340427)
      ·
        refine ⟨47732984270198439708510641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31821989513465626472340427 47732984270198439708510641)
        ·
          refine ⟨35799738202648829781382981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47732984270198439708510641 35799738202648829781382981)
          ·
            refine ⟨6712450912996655584009309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35799738202648829781382981 6712450912996655584009309)
            ·
              refine ⟨2517169092373745844003491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6712450912996655584009309 2517169092373745844003491)
              ·
                refine ⟨3775753638560618766005237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517169092373745844003491 3775753638560618766005237)
                ·
                  refine ⟨353976903615058009312991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3775753638560618766005237 353976903615058009312991)
                  ·
                    rfl

theorem cell22_3102154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_3102154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102154 prefixEnd_3102154 := by exact prefixLift 3102154
  have htrace : WordTrace (prefixWord ++ tailWord_3102154) baseStart_3102154 baseEnd_3102154 := by
    simpa [prefixWord, tailWord_3102154, baseEnd_3102154] using wordTrace_append hprefix tailTrace_3102154
  have hstable : (prefixWord ++ tailWord_3102154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102154).length < 2 ^ (prefixWord ++ tailWord_3102154).sum := by decide
  have hdescent : baseEnd_3102154 < baseStart_3102154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102195 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_3102195 : Nat := 118140960795 + 3102195 * 2 ^ 59
def prefixEnd_3102195 : Nat := 4983230072969 + 3 ^ 40 * 3102195 * 2
def baseEnd_3102195 : Nat := 1061944745983063587663847

theorem tailTrace_3102195 : CollatzResearch.WordTrace tailWord_3102195 prefixEnd_3102195 1061944745983063587663847 := by
  unfold tailWord_3102195
  simp only [CollatzResearch.WordTrace]
  refine ⟨113146346996284802570564039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75430897997523201713709359 113146346996284802570564039)
  ·
    refine ⟨169719520494427203855846059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113146346996284802570564039 169719520494427203855846059)
    ·
      refine ⟨254579280741640805783769089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169719520494427203855846059 254579280741640805783769089)
      ·
        refine ⟨190934460556230604337826817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254579280741640805783769089 190934460556230604337826817)
        ·
          refine ⟨143200845417172953253370113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190934460556230604337826817 143200845417172953253370113)
          ·
            refine ⟨107400634062879714940027585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143200845417172953253370113 107400634062879714940027585)
            ·
              refine ⟨80550475547159786205020689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107400634062879714940027585 80550475547159786205020689)
              ·
                refine ⟨60412856660369839653765517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80550475547159786205020689 60412856660369839653765517)
                ·
                  refine ⟨22654821247638689870162069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60412856660369839653765517 22654821247638689870162069)
                  ·
                    refine ⟨1061944745983063587663847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22654821247638689870162069 1061944745983063587663847)
                    ·
                      rfl

theorem cell22_3102195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_3102195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102195 prefixEnd_3102195 := by exact prefixLift 3102195
  have htrace : WordTrace (prefixWord ++ tailWord_3102195) baseStart_3102195 baseEnd_3102195 := by
    simpa [prefixWord, tailWord_3102195, baseEnd_3102195] using wordTrace_append hprefix tailTrace_3102195
  have hstable : (prefixWord ++ tailWord_3102195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102195).length < 2 ^ (prefixWord ++ tailWord_3102195).sum := by decide
  have hdescent : baseEnd_3102195 < baseStart_3102195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102229 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3102229 : Nat := 118140960795 + 3102229 * 2 ^ 59
def prefixEnd_3102229 : Nat := 4983230072969 + 3 ^ 40 * 3102229 * 2
def baseEnd_3102229 : Nat := 1061956384877898832313743

theorem tailTrace_3102229 : CollatzResearch.WordTrace tailWord_3102229 prefixEnd_3102229 1061956384877898832313743 := by
  unfold tailWord_3102229
  simp only [CollatzResearch.WordTrace]
  refine ⟨113147587078161626377301741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75431724718774417584867827 113147587078161626377301741)
  ·
    refine ⟨42430345154310609891488153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113147587078161626377301741 42430345154310609891488153)
    ·
      refine ⟨31822758865732957418616115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42430345154310609891488153 31822758865732957418616115)
      ·
        refine ⟨47734138298599436127924173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31822758865732957418616115 47734138298599436127924173)
        ·
          refine ⟨17900301861974788547971565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47734138298599436127924173 17900301861974788547971565)
          ·
            refine ⟨6712613198240545705489337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17900301861974788547971565 6712613198240545705489337)
            ·
              refine ⟨5034459898680409279117003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6712613198240545705489337 5034459898680409279117003)
              ·
                refine ⟨7551689848020613918675505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034459898680409279117003 7551689848020613918675505)
                ·
                  refine ⟨5663767386015460439006629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7551689848020613918675505 5663767386015460439006629)
                  ·
                    refine ⟨1061956384877898832313743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5663767386015460439006629 1061956384877898832313743)
                    ·
                      rfl

theorem cell22_3102229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3102229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102229 prefixEnd_3102229 := by exact prefixLift 3102229
  have htrace : WordTrace (prefixWord ++ tailWord_3102229) baseStart_3102229 baseEnd_3102229 := by
    simpa [prefixWord, tailWord_3102229, baseEnd_3102229] using wordTrace_append hprefix tailTrace_3102229
  have hstable : (prefixWord ++ tailWord_3102229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102229).length < 2 ^ (prefixWord ++ tailWord_3102229).sum := by decide
  have hdescent : baseEnd_3102229 < baseStart_3102229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102248 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3102248 : Nat := 118140960795 + 3102248 * 2 ^ 59
def prefixEnd_3102248 : Nat := 4983230072969 + 3 ^ 40 * 3102248 * 2
def baseEnd_3102248 : Nat := 1061962888966189116088685

theorem tailTrace_3102248 : CollatzResearch.WordTrace tailWord_3102248 prefixEnd_3102248 1061962888966189116088685 := by
  unfold tailWord_3102248
  simp only [CollatzResearch.WordTrace]
  refine ⟨56574140032546396311121699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75432186710061861748162265 56574140032546396311121699)
  ·
    refine ⟨84861210048819594466682549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56574140032546396311121699 84861210048819594466682549)
    ·
      refine ⟨7955738442076836981251489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84861210048819594466682549 7955738442076836981251489)
      ·
        refine ⟨5966803831557627735938617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7955738442076836981251489 5966803831557627735938617)
        ·
          refine ⟨4475102873668220801953963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5966803831557627735938617 4475102873668220801953963)
          ·
            refine ⟨6712654310502331202930945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475102873668220801953963 6712654310502331202930945)
            ·
              refine ⟨5034490732876748402198209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6712654310502331202930945 5034490732876748402198209)
              ·
                refine ⟨3775868049657561301648657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5034490732876748402198209 3775868049657561301648657)
                ·
                  refine ⟨2831901037243170976236493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3775868049657561301648657 2831901037243170976236493)
                  ·
                    refine ⟨1061962888966189116088685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2831901037243170976236493 1061962888966189116088685)
                    ·
                      rfl

theorem cell22_3102248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3102248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102248 prefixEnd_3102248 := by exact prefixLift 3102248
  have htrace : WordTrace (prefixWord ++ tailWord_3102248) baseStart_3102248 baseEnd_3102248 := by
    simpa [prefixWord, tailWord_3102248, baseEnd_3102248] using wordTrace_append hprefix tailTrace_3102248
  have hstable : (prefixWord ++ tailWord_3102248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102248).length < 2 ^ (prefixWord ++ tailWord_3102248).sum := by decide
  have hdescent : baseEnd_3102248 < baseStart_3102248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102278 : List Nat := [6, 1, 1, 1, 3, 1, 3, 6]
def baseStart_3102278 : Nat := 118140960795 + 3102278 * 2 ^ 59
def prefixEnd_3102278 : Nat := 4983230072969 + 3 ^ 40 * 3102278 * 2
def baseEnd_3102278 : Nat := 117997017619919893093177

theorem tailTrace_3102278 : CollatzResearch.WordTrace tailWord_3102278 prefixEnd_3102278 117997017619919893093177 := by
  unfold tailWord_3102278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535917945468253367057359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75432916169989405163890325 3535917945468253367057359)
  ·
    refine ⟨5303876918202380050586039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535917945468253367057359 5303876918202380050586039)
    ·
      refine ⟨7955815377303570075879059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5303876918202380050586039 7955815377303570075879059)
      ·
        refine ⟨11933723065955355113818589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7955815377303570075879059 11933723065955355113818589)
        ·
          refine ⟨4475146149733258167681971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11933723065955355113818589 4475146149733258167681971)
          ·
            refine ⟨6712719224599887251522957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475146149733258167681971 6712719224599887251522957)
            ·
              refine ⟨2517269709224957719321109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6712719224599887251522957 2517269709224957719321109)
              ·
                refine ⟨117997017619919893093177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2517269709224957719321109 117997017619919893093177)
                ·
                  rfl

theorem cell22_3102278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_3102278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102278 prefixEnd_3102278 := by exact prefixLift 3102278
  have htrace : WordTrace (prefixWord ++ tailWord_3102278) baseStart_3102278 baseEnd_3102278 := by
    simpa [prefixWord, tailWord_3102278, baseEnd_3102278] using wordTrace_append hprefix tailTrace_3102278
  have hstable : (prefixWord ++ tailWord_3102278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102278).length < 2 ^ (prefixWord ++ tailWord_3102278).sum := by decide
  have hdescent : baseEnd_3102278 < baseStart_3102278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102347 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_3102347 : Nat := 118140960795 + 3102347 * 2 ^ 59
def prefixEnd_3102347 : Nat := 4983230072969 + 3 ^ 40 * 3102347 * 2
def baseEnd_3102347 : Nat := 1061996778689385857863381

theorem tailTrace_3102347 : CollatzResearch.WordTrace tailWord_3102347 prefixEnd_3102347 1061996778689385857863381 := by
  unfold tailWord_3102347
  simp only [CollatzResearch.WordTrace]
  refine ⟨113151890891734132530097295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75434593927822755020064863 113151890891734132530097295)
  ·
    refine ⟨169727836337601198795145943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113151890891734132530097295 169727836337601198795145943)
    ·
      refine ⟨254591754506401798192718915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169727836337601198795145943 254591754506401798192718915)
      ·
        refine ⟨381887631759602697289078373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254591754506401798192718915 381887631759602697289078373)
        ·
          refine ⟨71603930954925505741702195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 381887631759602697289078373 71603930954925505741702195)
          ·
            refine ⟨107405896432388258612553293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71603930954925505741702195 107405896432388258612553293)
            ·
              refine ⟨40277211162145596979707485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107405896432388258612553293 40277211162145596979707485)
              ·
                refine ⟨15103954185804598867390307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40277211162145596979707485 15103954185804598867390307)
                ·
                  refine ⟨22655931278706898301085461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15103954185804598867390307 22655931278706898301085461)
                  ·
                    refine ⟨1061996778689385857863381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22655931278706898301085461 1061996778689385857863381)
                    ·
                      rfl

theorem cell22_3102347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_3102347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102347 prefixEnd_3102347 := by exact prefixLift 3102347
  have htrace : WordTrace (prefixWord ++ tailWord_3102347) baseStart_3102347 baseEnd_3102347 := by
    simpa [prefixWord, tailWord_3102347, baseEnd_3102347] using wordTrace_append hprefix tailTrace_3102347
  have hstable : (prefixWord ++ tailWord_3102347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102347).length < 2 ^ (prefixWord ++ tailWord_3102347).sum := by decide
  have hdescent : baseEnd_3102347 < baseStart_3102347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102368 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_3102368 : Nat := 118140960795 + 3102368 * 2 ^ 59
def prefixEnd_3102368 : Nat := 4983230072969 + 3 ^ 40 * 3102368 * 2
def baseEnd_3102368 : Nat := 354001322472849601029439

theorem tailTrace_3102368 : CollatzResearch.WordTrace tailWord_3102368 prefixEnd_3102368 354001322472849601029439 := by
  unfold tailWord_3102368
  simp only [CollatzResearch.WordTrace]
  refine ⟨56576328412329026558305879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75435104549772035411074505 56576328412329026558305879)
  ·
    refine ⟨84864492618493539837458819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56576328412329026558305879 84864492618493539837458819)
    ·
      refine ⟨127296738927740309756188229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84864492618493539837458819 127296738927740309756188229)
      ·
        refine ⟨23868138548951308079285293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127296738927740309756188229 23868138548951308079285293)
        ·
          refine ⟨8950551955856740529731985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23868138548951308079285293 8950551955856740529731985)
          ·
            refine ⟨6712913966892555397298989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8950551955856740529731985 6712913966892555397298989)
            ·
              refine ⟨2517342737584708273987121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6712913966892555397298989 2517342737584708273987121)
              ·
                refine ⟨1888007053188531205490341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517342737584708273987121 1888007053188531205490341)
                ·
                  refine ⟨354001322472849601029439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888007053188531205490341 354001322472849601029439)
                  ·
                    rfl

theorem cell22_3102368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_3102368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102368 prefixEnd_3102368 := by exact prefixLift 3102368
  have htrace : WordTrace (prefixWord ++ tailWord_3102368) baseStart_3102368 baseEnd_3102368 := by
    simpa [prefixWord, tailWord_3102368, baseEnd_3102368] using wordTrace_append hprefix tailTrace_3102368
  have hstable : (prefixWord ++ tailWord_3102368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102368).length < 2 ^ (prefixWord ++ tailWord_3102368).sum := by decide
  have hdescent : baseEnd_3102368 < baseStart_3102368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102462 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_3102462 : Nat := 118140960795 + 3102462 * 2 ^ 59
def prefixEnd_3102462 : Nat := 4983230072969 + 3 ^ 40 * 3102462 * 2
def baseEnd_3102462 : Nat := 1062036145539563891238029

theorem tailTrace_3102462 : CollatzResearch.WordTrace tailWord_3102462 prefixEnd_3102462 1062036145539563891238029 := by
  unfold tailWord_3102462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14144510660789688396316705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75437390190878338113689093 14144510660789688396316705)
  ·
    refine ⟨10608382995592266297237529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14144510660789688396316705 10608382995592266297237529)
    ·
      refine ⟨7956287246694199722928147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10608382995592266297237529 7956287246694199722928147)
      ·
        refine ⟨11934430870041299584392221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956287246694199722928147 11934430870041299584392221)
        ·
          refine ⟨4475411576265487344147083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11934430870041299584392221 4475411576265487344147083)
          ·
            refine ⟨6713117364398231016220625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475411576265487344147083 6713117364398231016220625)
            ·
              refine ⟨5034838023298673262165469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713117364398231016220625 5034838023298673262165469)
              ·
                refine ⟨1888064258737002473312051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5034838023298673262165469 1888064258737002473312051)
                ·
                  refine ⟨2832096388105503709968077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888064258737002473312051 2832096388105503709968077)
                  ·
                    refine ⟨1062036145539563891238029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832096388105503709968077 1062036145539563891238029)
                    ·
                      rfl

theorem cell22_3102462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_3102462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102462 prefixEnd_3102462 := by exact prefixLift 3102462
  have htrace : WordTrace (prefixWord ++ tailWord_3102462) baseStart_3102462 baseEnd_3102462 := by
    simpa [prefixWord, tailWord_3102462, baseEnd_3102462] using wordTrace_append hprefix tailTrace_3102462
  have hstable : (prefixWord ++ tailWord_3102462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102462).length < 2 ^ (prefixWord ++ tailWord_3102462).sum := by decide
  have hdescent : baseEnd_3102462 < baseStart_3102462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102499 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_3102499 : Nat := 118140960795 + 3102499 * 2 ^ 59
def prefixEnd_3102499 : Nat := 4983230072969 + 3 ^ 40 * 3102499 * 2
def baseEnd_3102499 : Nat := 1062048811395708128062915

theorem tailTrace_3102499 : CollatzResearch.WordTrace tailWord_3102499 prefixEnd_3102499 1062048811395708128062915 := by
  unfold tailWord_3102499
  simp only [CollatzResearch.WordTrace]
  refine ⟨113157434787183462489630551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75438289858122308326420367 113157434787183462489630551)
  ·
    refine ⟨169736152180775193734445827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113157434787183462489630551 169736152180775193734445827)
    ·
      refine ⟨254604228271162790601668741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169736152180775193734445827 254604228271162790601668741)
      ·
        refine ⟨47738292800843023237812889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254604228271162790601668741 47738292800843023237812889)
        ·
          refine ⟨35803719600632267428359667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47738292800843023237812889 35803719600632267428359667)
          ·
            refine ⟨53705579400948401142539501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35803719600632267428359667 53705579400948401142539501)
            ·
              refine ⟨20139592275355650428452313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53705579400948401142539501 20139592275355650428452313)
              ·
                refine ⟨15104694206516737821339235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20139592275355650428452313 15104694206516737821339235)
                ·
                  refine ⟨22657041309775106732008853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15104694206516737821339235 22657041309775106732008853)
                  ·
                    refine ⟨1062048811395708128062915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22657041309775106732008853 1062048811395708128062915)
                    ·
                      rfl

theorem cell22_3102499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_3102499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102499 prefixEnd_3102499 := by exact prefixLift 3102499
  have htrace : WordTrace (prefixWord ++ tailWord_3102499) baseStart_3102499 baseEnd_3102499 := by
    simpa [prefixWord, tailWord_3102499, baseEnd_3102499] using wordTrace_append hprefix tailTrace_3102499
  have hstable : (prefixWord ++ tailWord_3102499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102499).length < 2 ^ (prefixWord ++ tailWord_3102499).sum := by decide
  have hdescent : baseEnd_3102499 < baseStart_3102499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102501 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_3102501 : Nat := 118140960795 + 3102501 * 2 ^ 59
def prefixEnd_3102501 : Nat := 4983230072969 + 3 ^ 40 * 3102501 * 2
def baseEnd_3102501 : Nat := 1062049496036580789512909

theorem tailTrace_3102501 : CollatzResearch.WordTrace tailWord_3102501 prefixEnd_3102501 1062049496036580789512909 := by
  unfold tailWord_3102501
  simp only [CollatzResearch.WordTrace]
  refine ⟨113157507733176216831203357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75438338488784144554135571 113157507733176216831203357)
  ·
    refine ⟨42434065399941081311701259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113157507733176216831203357 42434065399941081311701259)
    ·
      refine ⟨63651098099911621967551889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42434065399941081311701259 63651098099911621967551889)
      ·
        refine ⟨47738323574933716475663917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63651098099911621967551889 47738323574933716475663917)
        ·
          refine ⟨17901871340600143678373969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47738323574933716475663917 17901871340600143678373969)
          ·
            refine ⟨13426403505450107758780477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17901871340600143678373969 13426403505450107758780477)
            ·
              refine ⟨5034901314543790409542679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13426403505450107758780477 5034901314543790409542679)
              ·
                refine ⟨7552351971815685614314019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5034901314543790409542679 7552351971815685614314019)
                ·
                  refine ⟨11328527957723528421471029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7552351971815685614314019 11328527957723528421471029)
                  ·
                    refine ⟨1062049496036580789512909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11328527957723528421471029 1062049496036580789512909)
                    ·
                      rfl

theorem cell22_3102501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_3102501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102501 prefixEnd_3102501 := by exact prefixLift 3102501
  have htrace : WordTrace (prefixWord ++ tailWord_3102501) baseStart_3102501 baseEnd_3102501 := by
    simpa [prefixWord, tailWord_3102501, baseEnd_3102501] using wordTrace_append hprefix tailTrace_3102501
  have hstable : (prefixWord ++ tailWord_3102501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102501).length < 2 ^ (prefixWord ++ tailWord_3102501).sum := by decide
  have hdescent : baseEnd_3102501 < baseStart_3102501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102544 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_3102544 : Nat := 118140960795 + 3102544 * 2 ^ 59
def prefixEnd_3102544 : Nat := 4983230072969 + 3 ^ 40 * 3102544 * 2
def baseEnd_3102544 : Nat := 1062064215815343010687777

theorem tailTrace_3102544 : CollatzResearch.WordTrace tailWord_3102544 prefixEnd_3102544 1062064215815343010687777 := by
  unfold tailWord_3102544
  simp only [CollatzResearch.WordTrace]
  refine ⟨56579538036010217587509343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75439384048013623450012457 56579538036010217587509343)
  ·
    refine ⟨84869307054015326381264015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56579538036010217587509343 84869307054015326381264015)
    ·
      refine ⟨127303960581022989571896023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84869307054015326381264015 127303960581022989571896023)
      ·
        refine ⟨190955940871534484357844035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127303960581022989571896023 190955940871534484357844035)
        ·
          refine ⟨286433911307301726536766053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190955940871534484357844035 286433911307301726536766053)
          ·
            refine ⟨53706358370119073725643635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286433911307301726536766053 53706358370119073725643635)
            ·
              refine ⟨80559537555178610588465453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53706358370119073725643635 80559537555178610588465453)
              ·
                refine ⟨30209826583191978970674545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80559537555178610588465453 30209826583191978970674545)
                ·
                  refine ⟨22657369937393984228005909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30209826583191978970674545 22657369937393984228005909)
                  ·
                    refine ⟨1062064215815343010687777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22657369937393984228005909 1062064215815343010687777)
                    ·
                      rfl

theorem cell22_3102544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_3102544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102544 prefixEnd_3102544 := by exact prefixLift 3102544
  have htrace : WordTrace (prefixWord ++ tailWord_3102544) baseStart_3102544 baseEnd_3102544 := by
    simpa [prefixWord, tailWord_3102544, baseEnd_3102544] using wordTrace_append hprefix tailTrace_3102544
  have hstable : (prefixWord ++ tailWord_3102544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102544).length < 2 ^ (prefixWord ++ tailWord_3102544).sum := by decide
  have hdescent : baseEnd_3102544 < baseStart_3102544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102614 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3102614 : Nat := 118140960795 + 3102614 * 2 ^ 59
def prefixEnd_3102614 : Nat := 4983230072969 + 3 ^ 40 * 3102614 * 2
def baseEnd_3102614 : Nat := 1062088178245886161437563

theorem tailTrace_3102614 : CollatzResearch.WordTrace tailWord_3102614 prefixEnd_3102614 1062088178245886161437563 := by
  unfold tailWord_3102614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072601823860427320629181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75441086121177891420044597 7072601823860427320629181)
  ·
    refine ⟨2652225683947660245235943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7072601823860427320629181 2652225683947660245235943)
    ·
      refine ⟨3978338525921490367853915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652225683947660245235943 3978338525921490367853915)
      ·
        refine ⟨5967507788882235551780873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978338525921490367853915 5967507788882235551780873)
        ·
          refine ⟨4475630841661676663835655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5967507788882235551780873 4475630841661676663835655)
          ·
            refine ⟨6713446262492514995753483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475630841661676663835655 6713446262492514995753483)
            ·
              refine ⟨10070169393738772493630225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713446262492514995753483 10070169393738772493630225)
              ·
                refine ⟨7552627045304079370222669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10070169393738772493630225 7552627045304079370222669)
                ·
                  refine ⟨2832235141989029763833501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7552627045304079370222669 2832235141989029763833501)
                  ·
                    refine ⟨1062088178245886161437563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832235141989029763833501 1062088178245886161437563)
                    ·
                      rfl

theorem cell22_3102614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3102614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102614 prefixEnd_3102614 := by exact prefixLift 3102614
  have htrace : WordTrace (prefixWord ++ tailWord_3102614) baseStart_3102614 baseEnd_3102614 := by
    simpa [prefixWord, tailWord_3102614, baseEnd_3102614] using wordTrace_append hprefix tailTrace_3102614
  have hstable : (prefixWord ++ tailWord_3102614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102614).length < 2 ^ (prefixWord ++ tailWord_3102614).sum := by decide
  have hdescent : baseEnd_3102614 < baseStart_3102614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102621 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3102621 : Nat := 118140960795 + 3102621 * 2 ^ 59
def prefixEnd_3102621 : Nat := 4983230072969 + 3 ^ 40 * 3102621 * 2
def baseEnd_3102621 : Nat := 354030191496313492170847

theorem tailTrace_3102621 : CollatzResearch.WordTrace tailWord_3102621 prefixEnd_3102621 354030191496313492170847 := by
  unfold tailWord_3102621
  simp only [CollatzResearch.WordTrace]
  refine ⟨113161884492741477325571717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75441256328494318217047811 113161884492741477325571717)
  ·
    refine ⟨21217853342389026998544697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113161884492741477325571717 21217853342389026998544697)
    ·
      refine ⟨15913390006791770248908523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21217853342389026998544697 15913390006791770248908523)
      ·
        refine ⟨23870085010187655373362785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15913390006791770248908523 23870085010187655373362785)
        ·
          refine ⟨17902563757640741530022089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23870085010187655373362785 17902563757640741530022089)
          ·
            refine ⟨13426922818230556147516567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17902563757640741530022089 13426922818230556147516567)
            ·
              refine ⟨20140384227345834221274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13426922818230556147516567 20140384227345834221274851)
              ·
                refine ⟨30210576341018751331912277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20140384227345834221274851 30210576341018751331912277)
                ·
                  refine ⟨354030191496313492170847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30210576341018751331912277 354030191496313492170847)
                  ·
                    rfl

theorem cell22_3102621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3102621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102621 prefixEnd_3102621 := by exact prefixLift 3102621
  have htrace : WordTrace (prefixWord ++ tailWord_3102621) baseStart_3102621 baseEnd_3102621 := by
    simpa [prefixWord, tailWord_3102621, baseEnd_3102621] using wordTrace_append hprefix tailTrace_3102621
  have hstable : (prefixWord ++ tailWord_3102621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102621).length < 2 ^ (prefixWord ++ tailWord_3102621).sum := by decide
  have hdescent : baseEnd_3102621 < baseStart_3102621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102644 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3102644 : Nat := 118140960795 + 3102644 * 2 ^ 59
def prefixEnd_3102644 : Nat := 4983230072969 + 3 ^ 40 * 3102644 * 2
def baseEnd_3102644 : Nat := 354032815952992027729157

theorem tailTrace_3102644 : CollatzResearch.WordTrace tailWord_3102644 prefixEnd_3102644 354032815952992027729157 := by
  unfold tailWord_3102644
  simp only [CollatzResearch.WordTrace]
  refine ⟨56581361685829076126829493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75441815581105434835772657 56581361685829076126829493)
  ·
    refine ⟨5304502658046475886890265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56581361685829076126829493 5304502658046475886890265)
    ·
      refine ⟨3978376993534856915167699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5304502658046475886890265 3978376993534856915167699)
      ·
        refine ⟨5967565490302285372751549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978376993534856915167699 5967565490302285372751549)
        ·
          refine ⟨2237837058863357014781831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5967565490302285372751549 2237837058863357014781831)
          ·
            refine ⟨3356755588295035522172747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237837058863357014781831 3356755588295035522172747)
            ·
              refine ⟨5035133382442553283259121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356755588295035522172747 5035133382442553283259121)
              ·
                refine ⟨3776350036831914962444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035133382442553283259121 3776350036831914962444341)
                ·
                  refine ⟨354032815952992027729157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3776350036831914962444341 354032815952992027729157)
                  ·
                    rfl

theorem cell22_3102644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3102644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102644 prefixEnd_3102644 := by exact prefixLift 3102644
  have htrace : WordTrace (prefixWord ++ tailWord_3102644) baseStart_3102644 baseEnd_3102644 := by
    simpa [prefixWord, tailWord_3102644, baseEnd_3102644] using wordTrace_append hprefix tailTrace_3102644
  have hstable : (prefixWord ++ tailWord_3102644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102644).length < 2 ^ (prefixWord ++ tailWord_3102644).sum := by decide
  have hdescent : baseEnd_3102644 < baseStart_3102644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102696 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3102696 : Nat := 118140960795 + 3102696 * 2 ^ 59
def prefixEnd_3102696 : Nat := 4983230072969 + 3 ^ 40 * 3102696 * 2
def baseEnd_3102696 : Nat := 1062116248521665280887311

theorem tailTrace_3102696 : CollatzResearch.WordTrace tailWord_3102696 prefixEnd_3102696 1062116248521665280887311 := by
  unfold tailWord_3102696
  simp only [CollatzResearch.WordTrace]
  refine ⟨56582309983734882567275971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75443079978313176756367961 56582309983734882567275971)
  ·
    refine ⟨84873464975602323850913957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56582309983734882567275971 84873464975602323850913957)
    ·
      refine ⟨15913774682925435722046367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84873464975602323850913957 15913774682925435722046367)
      ·
        refine ⟨23870662024388153583069551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15913774682925435722046367 23870662024388153583069551)
        ·
          refine ⟨35805993036582230374604327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23870662024388153583069551 35805993036582230374604327)
          ·
            refine ⟨53708989554873345561906491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35805993036582230374604327 53708989554873345561906491)
            ·
              refine ⟨80563484332310018342859737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53708989554873345561906491 80563484332310018342859737)
              ·
                refine ⟨60422613249232513757144803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80563484332310018342859737 60422613249232513757144803)
                ·
                  refine ⟨90633919873848770635717205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60422613249232513757144803 90633919873848770635717205)
                  ·
                    refine ⟨1062116248521665280887311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90633919873848770635717205 1062116248521665280887311)
                    ·
                      rfl

theorem cell22_3102696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3102696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102696 prefixEnd_3102696 := by exact prefixLift 3102696
  have htrace : WordTrace (prefixWord ++ tailWord_3102696) baseStart_3102696 baseEnd_3102696 := by
    simpa [prefixWord, tailWord_3102696, baseEnd_3102696] using wordTrace_append hprefix tailTrace_3102696
  have hstable : (prefixWord ++ tailWord_3102696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102696).length < 2 ^ (prefixWord ++ tailWord_3102696).sum := by decide
  have hdescent : baseEnd_3102696 < baseStart_3102696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102715 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 1, 3]
def baseStart_3102715 : Nat := 118140960795 + 3102715 * 2 ^ 59
def prefixEnd_3102715 : Nat := 4983230072969 + 3 ^ 40 * 3102715 * 2
def baseEnd_3102715 : Nat := 1062122752609955564662253

theorem tailTrace_3102715 : CollatzResearch.WordTrace tailWord_3102715 prefixEnd_3102715 1062122752609955564662253 := by
  unfold tailWord_3102715
  simp only [CollatzResearch.WordTrace]
  refine ⟨113165312954400931379493599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75443541969600620919662399 113165312954400931379493599)
  ·
    refine ⟨169747969431601397069240399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113165312954400931379493599 169747969431601397069240399)
    ·
      refine ⟨254621954147402095603860599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169747969431601397069240399 254621954147402095603860599)
      ·
        refine ⟨381932931221103143405790899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254621954147402095603860599 381932931221103143405790899)
        ·
          refine ⟨572899396831654715108686349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381932931221103143405790899 572899396831654715108686349)
          ·
            refine ⟨214837273811870518165757381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 572899396831654715108686349 214837273811870518165757381)
            ·
              refine ⟨40281988839725722156079509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214837273811870518165757381 40281988839725722156079509)
              ·
                refine ⟨1888218226862143226066227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40281988839725722156079509 1888218226862143226066227)
                ·
                  refine ⟨2832327340293214839099341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888218226862143226066227 2832327340293214839099341)
                  ·
                    refine ⟨1062122752609955564662253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832327340293214839099341 1062122752609955564662253)
                    ·
                      rfl

theorem cell22_3102715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 3].length) (baseStart_3102715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102715 prefixEnd_3102715 := by exact prefixLift 3102715
  have htrace : WordTrace (prefixWord ++ tailWord_3102715) baseStart_3102715 baseEnd_3102715 := by
    simpa [prefixWord, tailWord_3102715, baseEnd_3102715] using wordTrace_append hprefix tailTrace_3102715
  have hstable : (prefixWord ++ tailWord_3102715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102715).length < 2 ^ (prefixWord ++ tailWord_3102715).sum := by decide
  have hdescent : baseEnd_3102715 < baseStart_3102715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102728 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_3102728 : Nat := 118140960795 + 3102728 * 2 ^ 59
def prefixEnd_3102728 : Nat := 4983230072969 + 3 ^ 40 * 3102728 * 2
def baseEnd_3102728 : Nat := 354042400925209288029071

theorem tailTrace_3102728 : CollatzResearch.WordTrace tailWord_3102728 prefixEnd_3102728 354042400925209288029071 := by
  unfold tailWord_3102728
  simp only [CollatzResearch.WordTrace]
  refine ⟨56582893551676917299858419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75443858068902556399811225 56582893551676917299858419)
  ·
    refine ⟨84874340327515375949787629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56582893551676917299858419 84874340327515375949787629)
    ·
      refine ⟨31827877622818265981170361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84874340327515375949787629 31827877622818265981170361)
      ·
        refine ⟨23870908217113699485877771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31827877622818265981170361 23870908217113699485877771)
        ·
          refine ⟨35806362325670549228816657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23870908217113699485877771 35806362325670549228816657)
          ·
            refine ⟨26854771744252911921612493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35806362325670549228816657 26854771744252911921612493)
            ·
              refine ⟨10070539404094841970604685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26854771744252911921612493 10070539404094841970604685)
              ·
                refine ⟨3776452276535565738976757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10070539404094841970604685 3776452276535565738976757)
                ·
                  refine ⟨354042400925209288029071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3776452276535565738976757 354042400925209288029071)
                  ·
                    rfl

theorem cell22_3102728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_3102728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102728 prefixEnd_3102728 := by exact prefixLift 3102728
  have htrace : WordTrace (prefixWord ++ tailWord_3102728) baseStart_3102728 baseEnd_3102728 := by
    simpa [prefixWord, tailWord_3102728, baseEnd_3102728] using wordTrace_append hprefix tailTrace_3102728
  have hstable : (prefixWord ++ tailWord_3102728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102728).length < 2 ^ (prefixWord ++ tailWord_3102728).sum := by decide
  have hdescent : baseEnd_3102728 < baseStart_3102728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102766 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3102766 : Nat := 118140960795 + 3102766 * 2 ^ 59
def prefixEnd_3102766 : Nat := 4983230072969 + 3 ^ 40 * 3102766 * 2
def baseEnd_3102766 : Nat := 1062140210952208431637097

theorem tailTrace_3102766 : CollatzResearch.WordTrace tailWord_3102766 prefixEnd_3102766 1062140210952208431637097 := by
  unfold tailWord_3102766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145896634652020886200019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75444782051477444726400101 14145896634652020886200019)
  ·
    refine ⟨21218844951978031329300029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14145896634652020886200019 21218844951978031329300029)
    ·
      refine ⟨7957066856991761748487511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21218844951978031329300029 7957066856991761748487511)
      ·
        refine ⟨11935600285487642622731267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7957066856991761748487511 11935600285487642622731267)
        ·
          refine ⟨17903400428231463934096901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11935600285487642622731267 17903400428231463934096901)
          ·
            refine ⟨3356887580293399487643169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17903400428231463934096901 3356887580293399487643169)
            ·
              refine ⟨2517665685220049615732377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3356887580293399487643169 2517665685220049615732377)
              ·
                refine ⟨1888249263915037211799283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517665685220049615732377 1888249263915037211799283)
                ·
                  refine ⟨2832373895872555817698925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888249263915037211799283 2832373895872555817698925)
                  ·
                    refine ⟨1062140210952208431637097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832373895872555817698925 1062140210952208431637097)
                    ·
                      rfl

theorem cell22_3102766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3102766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102766 prefixEnd_3102766 := by exact prefixLift 3102766
  have htrace : WordTrace (prefixWord ++ tailWord_3102766) baseStart_3102766 baseEnd_3102766 := by
    simpa [prefixWord, tailWord_3102766, baseEnd_3102766] using wordTrace_append hprefix tailTrace_3102766
  have hstable : (prefixWord ++ tailWord_3102766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102766).length < 2 ^ (prefixWord ++ tailWord_3102766).sum := by decide
  have hdescent : baseEnd_3102766 < baseStart_3102766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102884 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_3102884 : Nat := 118140960795 + 3102884 * 2 ^ 59
def prefixEnd_3102884 : Nat := 4983230072969 + 3 ^ 40 * 3102884 * 2
def baseEnd_3102884 : Nat := 1062180604763695457186735

theorem tailTrace_3102884 : CollatzResearch.WordTrace tailWord_3102884 prefixEnd_3102884 1062180604763695457186735 := by
  unfold tailWord_3102884
  simp only [CollatzResearch.WordTrace]
  refine ⟨56585738445394336621197853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75447651260525782161597137 56585738445394336621197853)
  ·
    refine ⟨21219651917022876232949195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56585738445394336621197853 21219651917022876232949195)
    ·
      refine ⟨31829477875534314349423793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21219651917022876232949195 31829477875534314349423793)
      ·
        refine ⟨23872108406650735762067845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31829477875534314349423793 23872108406650735762067845)
        ·
          refine ⟨4476020326247012955387721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23872108406650735762067845 4476020326247012955387721)
          ·
            refine ⟨3357015244685259716540791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476020326247012955387721 3357015244685259716540791)
            ·
              refine ⟨5035522867027889574811187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357015244685259716540791 5035522867027889574811187)
              ·
                refine ⟨7553284300541834362216781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035522867027889574811187 7553284300541834362216781)
                ·
                  refine ⟨2832481612703187885831293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7553284300541834362216781 2832481612703187885831293)
                  ·
                    refine ⟨1062180604763695457186735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832481612703187885831293 1062180604763695457186735)
                    ·
                      rfl

theorem cell22_3102884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_3102884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102884 prefixEnd_3102884 := by exact prefixLift 3102884
  have htrace : WordTrace (prefixWord ++ tailWord_3102884) baseStart_3102884 baseEnd_3102884 := by
    simpa [prefixWord, tailWord_3102884, baseEnd_3102884] using wordTrace_append hprefix tailTrace_3102884
  have hstable : (prefixWord ++ tailWord_3102884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102884).length < 2 ^ (prefixWord ++ tailWord_3102884).sum := by decide
  have hdescent : baseEnd_3102884 < baseStart_3102884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102897 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 5]
def baseStart_3102897 : Nat := 118140960795 + 3102897 * 2 ^ 59
def prefixEnd_3102897 : Nat := 4983230072969 + 3 ^ 40 * 3102897 * 2
def baseEnd_3102897 : Nat := 354061684976455918870565

theorem tailTrace_3102897 : CollatzResearch.WordTrace tailWord_3102897 prefixEnd_3102897 354061684976455918870565 := by
  unfold tailWord_3102897
  simp only [CollatzResearch.WordTrace]
  refine ⟨113171951039741576462618945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75447967359827717641745963 113171951039741576462618945)
  ·
    refine ⟨84878963279806182346964209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113171951039741576462618945 84878963279806182346964209)
    ·
      refine ⟨63659222459854636760223157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84878963279806182346964209 63659222459854636760223157)
      ·
        refine ⟨5968052105611372196270921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63659222459854636760223157 5968052105611372196270921)
        ·
          refine ⟨4476039079208529147203191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968052105611372196270921 4476039079208529147203191)
          ·
            refine ⟨6714058618812793720804787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476039079208529147203191 6714058618812793720804787)
            ·
              refine ⟨10071087928219190581207181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714058618812793720804787 10071087928219190581207181)
              ·
                refine ⟨3776657973082196467952693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10071087928219190581207181 3776657973082196467952693)
                ·
                  refine ⟨354061684976455918870565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3776657973082196467952693 354061684976455918870565)
                  ·
                    rfl

theorem cell22_3102897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_3102897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102897 prefixEnd_3102897 := by exact prefixLift 3102897
  have htrace : WordTrace (prefixWord ++ tailWord_3102897) baseStart_3102897 baseEnd_3102897 := by
    simpa [prefixWord, tailWord_3102897, baseEnd_3102897] using wordTrace_append hprefix tailTrace_3102897
  have hstable : (prefixWord ++ tailWord_3102897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102897).length < 2 ^ (prefixWord ++ tailWord_3102897).sum := by decide
  have hdescent : baseEnd_3102897 < baseStart_3102897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102927 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 1, 4]
def baseStart_3102927 : Nat := 118140960795 + 3102927 * 2 ^ 59
def prefixEnd_3102927 : Nat := 4983230072969 + 3 ^ 40 * 3102927 * 2
def baseEnd_3102927 : Nat := 1062195324542457678361603

theorem tailTrace_3102927 : CollatzResearch.WordTrace tailWord_3102927 prefixEnd_3102927 1062195324542457678361603 := by
  unfold tailWord_3102927
  simp only [CollatzResearch.WordTrace]
  refine ⟨113173045229632891586211035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75448696819755261057474023 113173045229632891586211035)
  ·
    refine ⟨169759567844449337379316553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113173045229632891586211035 169759567844449337379316553)
    ·
      refine ⟨127319675883337003034487415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169759567844449337379316553 127319675883337003034487415)
      ·
        refine ⟨190979513825005504551731123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127319675883337003034487415 190979513825005504551731123)
        ·
          refine ⟨286469270737508256827596685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190979513825005504551731123 286469270737508256827596685)
          ·
            refine ⟨107425976526565596310348757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286469270737508256827596685 107425976526565596310348757)
            ·
              refine ⟨2517796324841381163523799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107425976526565596310348757 2517796324841381163523799)
              ·
                refine ⟨3776694487262071745285699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517796324841381163523799 3776694487262071745285699)
                ·
                  refine ⟨5665041730893107617928549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776694487262071745285699 5665041730893107617928549)
                  ·
                    refine ⟨1062195324542457678361603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665041730893107617928549 1062195324542457678361603)
                    ·
                      rfl

theorem cell22_3102927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_3102927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102927 prefixEnd_3102927 := by exact prefixLift 3102927
  have htrace : WordTrace (prefixWord ++ tailWord_3102927) baseStart_3102927 baseEnd_3102927 := by
    simpa [prefixWord, tailWord_3102927, baseEnd_3102927] using wordTrace_append hprefix tailTrace_3102927
  have hstable : (prefixWord ++ tailWord_3102927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102927).length < 2 ^ (prefixWord ++ tailWord_3102927).sum := by decide
  have hdescent : baseEnd_3102927 < baseStart_3102927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102946 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3102946 : Nat := 118140960795 + 3102946 * 2 ^ 59
def prefixEnd_3102946 : Nat := 4983230072969 + 3 ^ 40 * 3102946 * 2
def baseEnd_3102946 : Nat := 1062201828630747962136545

theorem tailTrace_3102946 : CollatzResearch.WordTrace tailWord_3102946 prefixEnd_3102946 1062201828630747962136545 := by
  unfold tailWord_3102946
  simp only [CollatzResearch.WordTrace]
  refine ⟨28293434554141014457788173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75449158811042705220768461 28293434554141014457788173)
  ·
    refine ⟨10610037957802880421670565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28293434554141014457788173 10610037957802880421670565)
    ·
      refine ⟨1989382117088040079063231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10610037957802880421670565 1989382117088040079063231)
      ·
        refine ⟨2984073175632060118594847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989382117088040079063231 2984073175632060118594847)
        ·
          refine ⟨4476109763448090177892271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984073175632060118594847 4476109763448090177892271)
          ·
            refine ⟨6714164645172135266838407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476109763448090177892271 6714164645172135266838407)
            ·
              refine ⟨10071246967758202900257611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714164645172135266838407 10071246967758202900257611)
              ·
                refine ⟨15106870451637304350386417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10071246967758202900257611 15106870451637304350386417)
                ·
                  refine ⟨11330152838727978262789813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15106870451637304350386417 11330152838727978262789813)
                  ·
                    refine ⟨1062201828630747962136545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11330152838727978262789813 1062201828630747962136545)
                    ·
                      rfl

theorem cell22_3102946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3102946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102946 prefixEnd_3102946 := by exact prefixLift 3102946
  have htrace : WordTrace (prefixWord ++ tailWord_3102946) baseStart_3102946 baseEnd_3102946 := by
    simpa [prefixWord, tailWord_3102946, baseEnd_3102946] using wordTrace_append hprefix tailTrace_3102946
  have hstable : (prefixWord ++ tailWord_3102946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102946).length < 2 ^ (prefixWord ++ tailWord_3102946).sum := by decide
  have hdescent : baseEnd_3102946 < baseStart_3102946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3102972 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_3102972 : Nat := 118140960795 + 3102972 * 2 ^ 59
def prefixEnd_3102972 : Nat := 4983230072969 + 3 ^ 40 * 3102972 * 2
def baseEnd_3102972 : Nat := 1062210728962092560986465

theorem tailTrace_3102972 : CollatzResearch.WordTrace tailWord_3102972 prefixEnd_3102972 1062210728962092560986465 := by
  unfold tailWord_3102972
  simp only [CollatzResearch.WordTrace]
  refine ⟨56587343257234932135799585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75449791009646576181066113 56587343257234932135799585)
  ·
    refine ⟨42440507442926199101849689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56587343257234932135799585 42440507442926199101849689)
    ·
      refine ⟨31830380582194649326387267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42440507442926199101849689 31830380582194649326387267)
      ·
        refine ⟨47745570873291973989580901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31830380582194649326387267 47745570873291973989580901)
        ·
          refine ⟨8952294538742245123046419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47745570873291973989580901 8952294538742245123046419)
          ·
            refine ⟨13428441808113367684569629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952294538742245123046419 13428441808113367684569629)
            ·
              refine ⟨5035665678042512881713611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13428441808113367684569629 5035665678042512881713611)
              ·
                refine ⟨7553498517063769322570417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035665678042512881713611 7553498517063769322570417)
                ·
                  refine ⟨5665123887797826991927813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7553498517063769322570417 5665123887797826991927813)
                  ·
                    refine ⟨1062210728962092560986465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665123887797826991927813 1062210728962092560986465)
                    ·
                      rfl

theorem cell22_3102972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_3102972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3102972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3102972 prefixEnd_3102972 := by exact prefixLift 3102972
  have htrace : WordTrace (prefixWord ++ tailWord_3102972) baseStart_3102972 baseEnd_3102972 := by
    simpa [prefixWord, tailWord_3102972, baseEnd_3102972] using wordTrace_append hprefix tailTrace_3102972
  have hstable : (prefixWord ++ tailWord_3102972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3102972).length < 2 ^ (prefixWord ++ tailWord_3102972).sum := by decide
  have hdescent : baseEnd_3102972 < baseStart_3102972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3102972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103021 : List Nat := [1, 5, 3, 1, 2, 2, 2, 6]
def baseStart_3103021 : Nat := 118140960795 + 3103021 * 2 ^ 59
def prefixEnd_3103021 : Nat := 4983230072969 + 3 ^ 40 * 3103021 * 2
def baseEnd_3103021 : Nat := 118025278073719196279035

theorem tailTrace_3103021 : CollatzResearch.WordTrace tailWord_3103021 prefixEnd_3103021 118025278073719196279035 := by
  unfold tailWord_3103021
  simp only [CollatzResearch.WordTrace]
  refine ⟨113176473691292345640132917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75450982460861563760088611 113176473691292345640132917)
  ·
    refine ⟨10610294408558657403762461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113176473691292345640132917 10610294408558657403762461)
    ·
      refine ⟨3978860403209496526410923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10610294408558657403762461 3978860403209496526410923)
      ·
        refine ⟨5968290604814244789616385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978860403209496526410923 5968290604814244789616385)
        ·
          refine ⟨4476217953610683592212289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968290604814244789616385 4476217953610683592212289)
          ·
            refine ⟨3357163465208012694159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476217953610683592212289 3357163465208012694159217)
            ·
              refine ⟨2517872598906009520619413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357163465208012694159217 2517872598906009520619413)
              ·
                refine ⟨118025278073719196279035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2517872598906009520619413 118025278073719196279035)
                ·
                  rfl

theorem cell22_3103021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 6].length) (baseStart_3103021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103021 prefixEnd_3103021 := by exact prefixLift 3103021
  have htrace : WordTrace (prefixWord ++ tailWord_3103021) baseStart_3103021 baseEnd_3103021 := by
    simpa [prefixWord, tailWord_3103021, baseEnd_3103021] using wordTrace_append hprefix tailTrace_3103021
  have hstable : (prefixWord ++ tailWord_3103021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103021).length < 2 ^ (prefixWord ++ tailWord_3103021).sum := by decide
  have hdescent : baseEnd_3103021 < baseStart_3103021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_3103045 : Nat := 118140960795 + 3103045 * 2 ^ 59
def prefixEnd_3103045 : Nat := 4983230072969 + 3 ^ 40 * 3103045 * 2
def baseEnd_3103045 : Nat := 1062235718353944703911241

theorem tailTrace_3103045 : CollatzResearch.WordTrace tailWord_3103045 prefixEnd_3103045 1062235718353944703911241 := by
  unfold tailWord_3103045
  simp only [CollatzResearch.WordTrace]
  refine ⟨113177349043205397739006589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75451566028803598492671059 113177349043205397739006589)
  ·
    refine ⟨42441505891202024152127471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113177349043205397739006589 42441505891202024152127471)
    ·
      refine ⟨63662258836803036228191207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42441505891202024152127471 63662258836803036228191207)
      ·
        refine ⟨95493388255204554342286811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63662258836803036228191207 95493388255204554342286811)
        ·
          refine ⟨143240082382806831513430217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95493388255204554342286811 143240082382806831513430217)
          ·
            refine ⟨107430061787105123635072663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143240082382806831513430217 107430061787105123635072663)
            ·
              refine ⟨161145092680657685452608995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107430061787105123635072663 161145092680657685452608995)
              ·
                refine ⟨241717639020986528178913493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161145092680657685452608995 241717639020986528178913493)
                ·
                  refine ⟨5665257164554371754193285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241717639020986528178913493 5665257164554371754193285)
                  ·
                    refine ⟨1062235718353944703911241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665257164554371754193285 1062235718353944703911241)
                    ·
                      rfl

theorem cell22_3103045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_3103045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103045 prefixEnd_3103045 := by exact prefixLift 3103045
  have htrace : WordTrace (prefixWord ++ tailWord_3103045) baseStart_3103045 baseEnd_3103045 := by
    simpa [prefixWord, tailWord_3103045, baseEnd_3103045] using wordTrace_append hprefix tailTrace_3103045
  have hstable : (prefixWord ++ tailWord_3103045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103045).length < 2 ^ (prefixWord ++ tailWord_3103045).sum := by decide
  have hdescent : baseEnd_3103045 < baseStart_3103045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103079 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3103079 : Nat := 118140960795 + 3103079 * 2 ^ 59
def prefixEnd_3103079 : Nat := 4983230072969 + 3 ^ 40 * 3103079 * 2
def baseEnd_3103079 : Nat := 1062247357248779948561137

theorem tailTrace_3103079 : CollatzResearch.WordTrace tailWord_3103079 prefixEnd_3103079 1062247357248779948561137 := by
  unfold tailWord_3103079
  simp only [CollatzResearch.WordTrace]
  refine ⟨113178589125082221545744291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75452392750054814363829527 113178589125082221545744291)
  ·
    refine ⟨169767883687623332318616437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113178589125082221545744291 169767883687623332318616437)
    ·
      refine ⟨15915739095714687404870291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169767883687623332318616437 15915739095714687404870291)
      ·
        refine ⟨23873608643572031107305437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15915739095714687404870291 23873608643572031107305437)
        ·
          refine ⟨8952603241339511665239539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23873608643572031107305437 8952603241339511665239539)
          ·
            refine ⟨13428904862009267497859309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952603241339511665239539 13428904862009267497859309)
            ·
              refine ⟨5035839323253475311697241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13428904862009267497859309 5035839323253475311697241)
              ·
                refine ⟨3776879492440106483772931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035839323253475311697241 3776879492440106483772931)
                ·
                  refine ⟨5665319238660159725659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776879492440106483772931 5665319238660159725659397)
                  ·
                    refine ⟨1062247357248779948561137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665319238660159725659397 1062247357248779948561137)
                    ·
                      rfl

theorem cell22_3103079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3103079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103079 prefixEnd_3103079 := by exact prefixLift 3103079
  have htrace : WordTrace (prefixWord ++ tailWord_3103079) baseStart_3103079 baseEnd_3103079 := by
    simpa [prefixWord, tailWord_3103079, baseEnd_3103079] using wordTrace_append hprefix tailTrace_3103079
  have hstable : (prefixWord ++ tailWord_3103079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103079).length < 2 ^ (prefixWord ++ tailWord_3103079).sum := by decide
  have hdescent : baseEnd_3103079 < baseStart_3103079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103156 : List Nat := [2, 5, 2, 2, 1, 1, 9]
def baseStart_3103156 : Nat := 118140960795 + 3103156 * 2 ^ 59
def prefixEnd_3103156 : Nat := 4983230072969 + 3 ^ 40 * 3103156 * 2
def baseEnd_3103156 : Nat := 39343470960088052384663

theorem tailTrace_3103156 : CollatzResearch.WordTrace tailWord_3103156 prefixEnd_3103156 39343470960088052384663 := by
  unfold tailWord_3103156
  simp only [CollatzResearch.WordTrace]
  refine ⟨56590698772901631848148661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75454265030535509130864881 56590698772901631848148661)
  ·
    refine ⟨5305378009959527985763937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56590698772901631848148661 5305378009959527985763937)
    ·
      refine ⟨3979033507469645989322953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5305378009959527985763937 3979033507469645989322953)
      ·
        refine ⟨2984275130602234491992215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979033507469645989322953 2984275130602234491992215)
        ·
          refine ⟨4476412695903351737988323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984275130602234491992215 4476412695903351737988323)
          ·
            refine ⟨6714619043855027606982485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476412695903351737988323 6714619043855027606982485)
            ·
              refine ⟨39343470960088052384663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6714619043855027606982485 39343470960088052384663)
              ·
                rfl

theorem cell22_3103156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 9].length) (baseStart_3103156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103156 prefixEnd_3103156 := by exact prefixLift 3103156
  have htrace : WordTrace (prefixWord ++ tailWord_3103156) baseStart_3103156 baseEnd_3103156 := by
    simpa [prefixWord, tailWord_3103156, baseEnd_3103156] using wordTrace_append hprefix tailTrace_3103156
  have hstable : (prefixWord ++ tailWord_3103156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103156).length < 2 ^ (prefixWord ++ tailWord_3103156).sum := by decide
  have hdescent : baseEnd_3103156 < baseStart_3103156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103205 : List Nat := [1, 3, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_3103205 : Nat := 118140960795 + 3103205 * 2 ^ 59
def prefixEnd_3103205 : Nat := 4983230072969 + 3 ^ 40 * 3103205 * 2
def baseEnd_3103205 : Nat := 1062290489623757619910751

theorem tailTrace_3103205 : CollatzResearch.WordTrace tailWord_3103205 prefixEnd_3103205 1062290489623757619910751 := by
  unfold tailWord_3103205
  simp only [CollatzResearch.WordTrace]
  refine ⟨113183184722625745064831069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75455456481750496709887379 113183184722625745064831069)
  ·
    refine ⟨42443694270984654399311651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113183184722625745064831069 42443694270984654399311651)
    ·
      refine ⟨63665541406476981598967477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42443694270984654399311651 63665541406476981598967477)
      ·
        refine ⟨5968644506857217024903201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63665541406476981598967477 5968644506857217024903201)
        ·
          refine ⟨4476483380142912768677401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968644506857217024903201 4476483380142912768677401)
          ·
            refine ⟨3357362535107184576508051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4476483380142912768677401 3357362535107184576508051)
            ·
              refine ⟨5036043802660776864762077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357362535107184576508051 5036043802660776864762077)
              ·
                refine ⟨1888516425997791324285779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5036043802660776864762077 1888516425997791324285779)
                ·
                  refine ⟨2832774638996686986428669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888516425997791324285779 2832774638996686986428669)
                  ·
                    refine ⟨1062290489623757619910751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832774638996686986428669 1062290489623757619910751)
                    ·
                      rfl

theorem cell22_3103205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_3103205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103205 prefixEnd_3103205 := by exact prefixLift 3103205
  have htrace : WordTrace (prefixWord ++ tailWord_3103205) baseStart_3103205 baseEnd_3103205 := by
    simpa [prefixWord, tailWord_3103205, baseEnd_3103205] using wordTrace_append hprefix tailTrace_3103205
  have hstable : (prefixWord ++ tailWord_3103205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103205).length < 2 ^ (prefixWord ++ tailWord_3103205).sum := by decide
  have hdescent : baseEnd_3103205 < baseStart_3103205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103287 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3103287 : Nat := 118140960795 + 3103287 * 2 ^ 59
def prefixEnd_3103287 : Nat := 4983230072969 + 3 ^ 40 * 3103287 * 2
def baseEnd_3103287 : Nat := 1062318559899536739360499

theorem tailTrace_3103287 : CollatzResearch.WordTrace tailWord_3103287 prefixEnd_3103287 1062318559899536739360499 := by
  unfold tailWord_3103287
  simp only [CollatzResearch.WordTrace]
  refine ⟨113186175508328673069316115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75457450338885782046210743 113186175508328673069316115)
  ·
    refine ⟨169779263262493009603974173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113186175508328673069316115 169779263262493009603974173)
    ·
      refine ⟨63667223723434878601490315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169779263262493009603974173 63667223723434878601490315)
      ·
        refine ⟨95500835585152317902235473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63667223723434878601490315 95500835585152317902235473)
        ·
          refine ⟨71625626688864238426676605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95500835585152317902235473 71625626688864238426676605)
          ·
            refine ⟨26859610008324089410003727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71625626688864238426676605 26859610008324089410003727)
            ·
              refine ⟨40289415012486134115005591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26859610008324089410003727 40289415012486134115005591)
              ·
                refine ⟨60434122518729201172508387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40289415012486134115005591 60434122518729201172508387)
                ·
                  refine ⟨90651183778093801758762581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60434122518729201172508387 90651183778093801758762581)
                  ·
                    refine ⟨1062318559899536739360499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90651183778093801758762581 1062318559899536739360499)
                    ·
                      rfl

theorem cell22_3103287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3103287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103287 prefixEnd_3103287 := by exact prefixLift 3103287
  have htrace : WordTrace (prefixWord ++ tailWord_3103287) baseStart_3103287 baseEnd_3103287 := by
    simpa [prefixWord, tailWord_3103287, baseEnd_3103287] using wordTrace_append hprefix tailTrace_3103287
  have hstable : (prefixWord ++ tailWord_3103287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103287).length < 2 ^ (prefixWord ++ tailWord_3103287).sum := by decide
  have hdescent : baseEnd_3103287 < baseStart_3103287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103306 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_3103306 : Nat := 118140960795 + 3103306 * 2 ^ 59
def prefixEnd_3103306 : Nat := 4983230072969 + 3 ^ 40 * 3103306 * 2
def baseEnd_3103306 : Nat := 1062325063987827023135441

theorem tailTrace_3103306 : CollatzResearch.WordTrace tailWord_3103306 prefixEnd_3103306 1062325063987827023135441 := by
  unfold tailWord_3103306
  simp only [CollatzResearch.WordTrace]
  refine ⟨28296717123814959828564443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75457912330173226209505181 28296717123814959828564443)
  ·
    refine ⟨42445075685722439742846665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28296717123814959828564443 42445075685722439742846665)
    ·
      refine ⟨31833806764291829807134999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42445075685722439742846665 31833806764291829807134999)
      ·
        refine ⟨47750710146437744710702499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31833806764291829807134999 47750710146437744710702499)
        ·
          refine ⟨71626065219656617066053749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47750710146437744710702499 71626065219656617066053749)
          ·
            refine ⟨6714943614342807849942539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71626065219656617066053749 6714943614342807849942539)
            ·
              refine ⟨10072415421514211774913809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714943614342807849942539 10072415421514211774913809)
              ·
                refine ⟨7554311566135658831185357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10072415421514211774913809 7554311566135658831185357)
                ·
                  refine ⟨2832866837300872061694509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7554311566135658831185357 2832866837300872061694509)
                  ·
                    refine ⟨1062325063987827023135441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832866837300872061694509 1062325063987827023135441)
                    ·
                      rfl

theorem cell22_3103306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_3103306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103306 prefixEnd_3103306 := by exact prefixLift 3103306
  have htrace : WordTrace (prefixWord ++ tailWord_3103306) baseStart_3103306 baseEnd_3103306 := by
    simpa [prefixWord, tailWord_3103306, baseEnd_3103306] using wordTrace_append hprefix tailTrace_3103306
  have hstable : (prefixWord ++ tailWord_3103306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103306).length < 2 ^ (prefixWord ++ tailWord_3103306).sum := by decide
  have hdescent : baseEnd_3103306 < baseStart_3103306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103336 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_3103336 : Nat := 118140960795 + 3103336 * 2 ^ 59
def prefixEnd_3103336 : Nat := 4983230072969 + 3 ^ 40 * 3103336 * 2
def baseEnd_3103336 : Nat := 354111777866972314961783

theorem tailTrace_3103336 : CollatzResearch.WordTrace tailWord_3103336 prefixEnd_3103336 354111777866972314961783 := by
  unfold tailWord_3103336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56593981342575577218924931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75458641790100769625233241 56593981342575577218924931)
  ·
    refine ⟨84890972013863365828387397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56593981342575577218924931 84890972013863365828387397)
    ·
      refine ⟨15917057252599381092822637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84890972013863365828387397 15917057252599381092822637)
      ·
        refine ⟨5968896469724767909808489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15917057252599381092822637 5968896469724767909808489)
        ·
          refine ⟨4476672352293575932356367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5968896469724767909808489 4476672352293575932356367)
          ·
            refine ⟨6715008528440363898534551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476672352293575932356367 6715008528440363898534551)
            ·
              refine ⟨10072512792660545847801827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715008528440363898534551 10072512792660545847801827)
              ·
                refine ⟨15108769188990818771702741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10072512792660545847801827 15108769188990818771702741)
                ·
                  refine ⟨354111777866972314961783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15108769188990818771702741 354111777866972314961783)
                  ·
                    rfl

theorem cell22_3103336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_3103336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103336 prefixEnd_3103336 := by exact prefixLift 3103336
  have htrace : WordTrace (prefixWord ++ tailWord_3103336) baseStart_3103336 baseEnd_3103336 := by
    simpa [prefixWord, tailWord_3103336, baseEnd_3103336] using wordTrace_append hprefix tailTrace_3103336
  have hstable : (prefixWord ++ tailWord_3103336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103336).length < 2 ^ (prefixWord ++ tailWord_3103336).sum := by decide
  have hdescent : baseEnd_3103336 < baseStart_3103336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103396 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_3103396 : Nat := 118140960795 + 3103396 * 2 ^ 59
def prefixEnd_3103396 : Nat := 4983230072969 + 3 ^ 40 * 3103396 * 2
def baseEnd_3103396 : Nat := 1062355872827096788385165

theorem tailTrace_3103396 : CollatzResearch.WordTrace tailWord_3103396 prefixEnd_3103396 1062355872827096788385165 := by
  unfold tailWord_3103396
  simp only [CollatzResearch.WordTrace]
  refine ⟨56595075532466892342517021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75460100709955856456689361 56595075532466892342517021)
  ·
    refine ⟨21223153324675084628443883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56595075532466892342517021 21223153324675084628443883)
    ·
      refine ⟨31834729987012626942665825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21223153324675084628443883 31834729987012626942665825)
      ·
        refine ⟨23876047490259470206999369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31834729987012626942665825 23876047490259470206999369)
        ·
          refine ⟨17907035617694602655249527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23876047490259470206999369 17907035617694602655249527)
          ·
            refine ⟨26860553426541903982874291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17907035617694602655249527 26860553426541903982874291)
            ·
              refine ⟨40290830139812855974311437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26860553426541903982874291 40290830139812855974311437)
              ·
                refine ⟨15109061302429820990366789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40290830139812855974311437 15109061302429820990366789)
                ·
                  refine ⟨2832948994205591435693773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15109061302429820990366789 2832948994205591435693773)
                  ·
                    refine ⟨1062355872827096788385165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832948994205591435693773 1062355872827096788385165)
                    ·
                      rfl

theorem cell22_3103396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_3103396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103396 prefixEnd_3103396 := by exact prefixLift 3103396
  have htrace : WordTrace (prefixWord ++ tailWord_3103396) baseStart_3103396 baseEnd_3103396 := by
    simpa [prefixWord, tailWord_3103396, baseEnd_3103396] using wordTrace_append hprefix tailTrace_3103396
  have hstable : (prefixWord ++ tailWord_3103396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103396).length < 2 ^ (prefixWord ++ tailWord_3103396).sum := by decide
  have hdescent : baseEnd_3103396 < baseStart_3103396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103428 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3103428 : Nat := 118140960795 + 3103428 * 2 ^ 59
def prefixEnd_3103428 : Nat := 4983230072969 + 3 ^ 40 * 3103428 * 2
def baseEnd_3103428 : Nat := 1062366827081059371585067

theorem tailTrace_3103428 : CollatzResearch.WordTrace tailWord_3103428 prefixEnd_3103428 1062366827081059371585067 := by
  unfold tailWord_3103428
  simp only [CollatzResearch.WordTrace]
  refine ⟨56595659100408927075099469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75460878800545236100132625 56595659100408927075099469)
  ·
    refine ⟨21223372162653347653162301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56595659100408927075099469 21223372162653347653162301)
    ·
      refine ⟨7958764560995005369935863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21223372162653347653162301 7958764560995005369935863)
      ·
        refine ⟨11938146841492508054903795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7958764560995005369935863 11938146841492508054903795)
        ·
          refine ⟨17907220262238762082355693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11938146841492508054903795 17907220262238762082355693)
          ·
            refine ⟨6715207598339535780883385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17907220262238762082355693 6715207598339535780883385)
            ·
              refine ⟨5036405698754651835662539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715207598339535780883385 5036405698754651835662539)
              ·
                refine ⟨7554608548131977753493809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036405698754651835662539 7554608548131977753493809)
                ·
                  refine ⟨5665956411098983315120357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7554608548131977753493809 5665956411098983315120357)
                  ·
                    refine ⟨1062366827081059371585067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665956411098983315120357 1062366827081059371585067)
                    ·
                      rfl

theorem cell22_3103428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3103428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103428 prefixEnd_3103428 := by exact prefixLift 3103428
  have htrace : WordTrace (prefixWord ++ tailWord_3103428) baseStart_3103428 baseEnd_3103428 := by
    simpa [prefixWord, tailWord_3103428, baseEnd_3103428] using wordTrace_append hprefix tailTrace_3103428
  have hstable : (prefixWord ++ tailWord_3103428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103428).length < 2 ^ (prefixWord ++ tailWord_3103428).sum := by decide
  have hdescent : baseEnd_3103428 < baseStart_3103428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103471 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 5]
def baseStart_3103471 : Nat := 118140960795 + 3103471 * 2 ^ 59
def prefixEnd_3103471 : Nat := 4983230072969 + 3 ^ 40 * 3103471 * 2
def baseEnd_3103471 : Nat := 354127182286607197586645

theorem tailTrace_3103471 : CollatzResearch.WordTrace tailWord_3103471 prefixEnd_3103471 354127182286607197586645 := by
  unfold tailWord_3103471
  simp only [CollatzResearch.WordTrace]
  refine ⟨113192886539662072494014267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75461924359774714996009511 113192886539662072494014267)
  ·
    refine ⟨169789329809493108741021401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113192886539662072494014267 169789329809493108741021401)
    ·
      refine ⟨127341997357119831555766051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169789329809493108741021401 127341997357119831555766051)
      ·
        refine ⟨191012996035679747333649077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127341997357119831555766051 191012996035679747333649077)
        ·
          refine ⟨17907468378344976312529601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191012996035679747333649077 17907468378344976312529601)
          ·
            refine ⟨13430601283758732234397201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17907468378344976312529601 13430601283758732234397201)
            ·
              refine ⟨10072950962819049175797901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13430601283758732234397201 10072950962819049175797901)
              ·
                refine ⟨3777356611057143440924213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10072950962819049175797901 3777356611057143440924213)
                ·
                  refine ⟨354127182286607197586645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3777356611057143440924213 354127182286607197586645)
                  ·
                    rfl

theorem cell22_3103471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 5].length) (baseStart_3103471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103471 prefixEnd_3103471 := by exact prefixLift 3103471
  have htrace : WordTrace (prefixWord ++ tailWord_3103471) baseStart_3103471 baseEnd_3103471 := by
    simpa [prefixWord, tailWord_3103471, baseEnd_3103471] using wordTrace_append hprefix tailTrace_3103471
  have hstable : (prefixWord ++ tailWord_3103471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103471).length < 2 ^ (prefixWord ++ tailWord_3103471).sum := by decide
  have hdescent : baseEnd_3103471 < baseStart_3103471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103477 : List Nat := [1, 3, 6, 1, 1, 1, 3, 6]
def baseStart_3103477 : Nat := 118140960795 + 3103477 * 2 ^ 59
def prefixEnd_3103477 : Nat := 4983230072969 + 3 ^ 40 * 3103477 * 2
def baseEnd_3103477 : Nat := 118042622309159953012213

theorem tailTrace_3103477 : CollatzResearch.WordTrace tailWord_3103477 prefixEnd_3103477 118042622309159953012213 := by
  unfold tailWord_3103477
  simp only [CollatzResearch.WordTrace]
  refine ⟨113193105377640335518732685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75462070251760223679155123 113193105377640335518732685)
  ·
    refine ⟨42447414516615125819524757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113193105377640335518732685 42447414516615125819524757)
    ·
      refine ⟨1989722555466334022790223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42447414516615125819524757 1989722555466334022790223)
      ·
        refine ⟨2984583833199501034185335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989722555466334022790223 2984583833199501034185335)
        ·
          refine ⟨4476875749799251551278003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984583833199501034185335 4476875749799251551278003)
          ·
            refine ⟨6715313624698877326917005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476875749799251551278003 6715313624698877326917005)
            ·
              refine ⟨2518242609262078997593877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6715313624698877326917005 2518242609262078997593877)
              ·
                refine ⟨118042622309159953012213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2518242609262078997593877 118042622309159953012213)
                ·
                  rfl

theorem cell22_3103477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 6].length) (baseStart_3103477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103477 prefixEnd_3103477 := by exact prefixLift 3103477
  have htrace : WordTrace (prefixWord ++ tailWord_3103477) baseStart_3103477 baseEnd_3103477 := by
    simpa [prefixWord, tailWord_3103477, baseEnd_3103477] using wordTrace_append hprefix tailTrace_3103477
  have hstable : (prefixWord ++ tailWord_3103477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103477).length < 2 ^ (prefixWord ++ tailWord_3103477).sum := by decide
  have hdescent : baseEnd_3103477 < baseStart_3103477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103499 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 10]
def baseStart_3103499 : Nat := 118140960795 + 3103499 * 2 ^ 59
def prefixEnd_3103499 : Nat := 4983230072969 + 3 ^ 40 * 3103499 * 2
def baseEnd_3103499 : Nat := 354130377277346284353283

theorem tailTrace_3103499 : CollatzResearch.WordTrace tailWord_3103499 prefixEnd_3103499 354130377277346284353283 := by
  unfold tailWord_3103499
  simp only [CollatzResearch.WordTrace]
  refine ⟨113193907783560633276033551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75462605189040422184022367 113193907783560633276033551)
  ·
    refine ⟨169790861675340949914050327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113193907783560633276033551 169790861675340949914050327)
    ·
      refine ⟨254686292513011424871075491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169790861675340949914050327 254686292513011424871075491)
      ·
        refine ⟨382029438769517137306613237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254686292513011424871075491 382029438769517137306613237)
        ·
          refine ⟨35815259884642231622494991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382029438769517137306613237 35815259884642231622494991)
          ·
            refine ⟨53722889826963347433742487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35815259884642231622494991 53722889826963347433742487)
            ·
              refine ⟨80584334740445021150613731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53722889826963347433742487 80584334740445021150613731)
              ·
                refine ⟨120876502110667531725920597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80584334740445021150613731 120876502110667531725920597)
                ·
                  refine ⟨354130377277346284353283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120876502110667531725920597 354130377277346284353283)
                  ·
                    rfl

theorem cell22_3103499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_3103499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103499 prefixEnd_3103499 := by exact prefixLift 3103499
  have htrace : WordTrace (prefixWord ++ tailWord_3103499) baseStart_3103499 baseEnd_3103499 := by
    simpa [prefixWord, tailWord_3103499, baseEnd_3103499] using wordTrace_append hprefix tailTrace_3103499
  have hstable : (prefixWord ++ tailWord_3103499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103499).length < 2 ^ (prefixWord ++ tailWord_3103499).sum := by decide
  have hdescent : baseEnd_3103499 < baseStart_3103499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103516 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_3103516 : Nat := 118140960795 + 3103516 * 2 ^ 59
def prefixEnd_3103516 : Nat := 4983230072969 + 3 ^ 40 * 3103516 * 2
def baseEnd_3103516 : Nat := 354132317093152158461599

theorem tailTrace_3103516 : CollatzResearch.WordTrace tailWord_3103516 prefixEnd_3103516 354132317093152158461599 := by
  unfold tailWord_3103516
  simp only [CollatzResearch.WordTrace]
  refine ⟨56597263912249522589701201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75463018549666030119601601 56597263912249522589701201)
  ·
    refine ⟨42447947934187141942275901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56597263912249522589701201 42447947934187141942275901)
    ·
      refine ⟨15917980475320178228353463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42447947934187141942275901 15917980475320178228353463)
      ·
        refine ⟨23876970712980267342530195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15917980475320178228353463 23876970712980267342530195)
        ·
          refine ⟨35815456069470401013795293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23876970712980267342530195 35815456069470401013795293)
          ·
            refine ⟨13430796026051400380173235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35815456069470401013795293 13430796026051400380173235)
            ·
              refine ⟨20146194039077100570259853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13430796026051400380173235 20146194039077100570259853)
              ·
                refine ⟨7554822764653912713847445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20146194039077100570259853 7554822764653912713847445)
                ·
                  refine ⟨354132317093152158461599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7554822764653912713847445 354132317093152158461599)
                  ·
                    rfl

theorem cell22_3103516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_3103516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103516 prefixEnd_3103516 := by exact prefixLift 3103516
  have htrace : WordTrace (prefixWord ++ tailWord_3103516) baseStart_3103516 baseEnd_3103516 := by
    simpa [prefixWord, tailWord_3103516, baseEnd_3103516] using wordTrace_append hprefix tailTrace_3103516
  have hstable : (prefixWord ++ tailWord_3103516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103516).length < 2 ^ (prefixWord ++ tailWord_3103516).sum := by decide
  have hdescent : baseEnd_3103516 < baseStart_3103516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103531 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 6, 3]
def baseStart_3103531 : Nat := 118140960795 + 3103531 * 2 ^ 59
def prefixEnd_3103531 : Nat := 4983230072969 + 3 ^ 40 * 3103531 * 2
def baseEnd_3103531 : Nat := 1062402086086001436259751

theorem tailTrace_3103531 : CollatzResearch.WordTrace tailWord_3103531 prefixEnd_3103531 1062402086086001436259751 := by
  unfold tailWord_3103531
  simp only [CollatzResearch.WordTrace]
  refine ⟨113195074919444702741198447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75463383279629801827465631 113195074919444702741198447)
  ·
    refine ⟨169792612379167054111797671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113195074919444702741198447 169792612379167054111797671)
    ·
      refine ⟨254688918568750581167696507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169792612379167054111797671 254688918568750581167696507)
      ·
        refine ⟨382033377853125871751544761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254688918568750581167696507 382033377853125871751544761)
        ·
          refine ⟨286525033389844403813658571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382033377853125871751544761 286525033389844403813658571)
          ·
            refine ⟨429787550084766605720487857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286525033389844403813658571 429787550084766605720487857)
            ·
              refine ⟨322340662563574954290365893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429787550084766605720487857 322340662563574954290365893)
              ·
                refine ⟨60438874230670303929443605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322340662563574954290365893 60438874230670303929443605)
                ·
                  refine ⟨2833072229562670496692669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60438874230670303929443605 2833072229562670496692669)
                  ·
                    refine ⟨1062402086086001436259751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833072229562670496692669 1062402086086001436259751)
                    ·
                      rfl

theorem cell22_3103531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 3].length) (baseStart_3103531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103531 prefixEnd_3103531 := by exact prefixLift 3103531
  have htrace : WordTrace (prefixWord ++ tailWord_3103531) baseStart_3103531 baseEnd_3103531 := by
    simpa [prefixWord, tailWord_3103531, baseEnd_3103531] using wordTrace_append hprefix tailTrace_3103531
  have hstable : (prefixWord ++ tailWord_3103531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103531).length < 2 ^ (prefixWord ++ tailWord_3103531).sum := by decide
  have hdescent : baseEnd_3103531 < baseStart_3103531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103561 : List Nat := [1, 2, 1, 1, 2, 7, 8]
def baseStart_3103561 : Nat := 118140960795 + 3103561 * 2 ^ 59
def prefixEnd_3103561 : Nat := 4983230072969 + 3 ^ 40 * 3103561 * 2
def baseEnd_3103561 : Nat := 39348605766633013259617

theorem tailTrace_3103561 : CollatzResearch.WordTrace tailWord_3103561 prefixEnd_3103561 39348605766633013259617 := by
  unfold tailWord_3103561
  simp only [CollatzResearch.WordTrace]
  refine ⟨113196169109336017864790537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75464112739557345243193691 113196169109336017864790537)
  ·
    refine ⟨84897126832002013398592903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113196169109336017864790537 84897126832002013398592903)
    ·
      refine ⟨127345690248003020097889355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84897126832002013398592903 127345690248003020097889355)
      ·
        refine ⟨191018535372004530146834033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127345690248003020097889355 191018535372004530146834033)
        ·
          refine ⟨143263901529003397610125525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191018535372004530146834033 143263901529003397610125525)
          ·
            refine ⟨3357747692086017131487317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143263901529003397610125525 3357747692086017131487317)
            ·
              refine ⟨39348605766633013259617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3357747692086017131487317 39348605766633013259617)
              ·
                rfl

theorem cell22_3103561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 8].length) (baseStart_3103561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103561 prefixEnd_3103561 := by exact prefixLift 3103561
  have htrace : WordTrace (prefixWord ++ tailWord_3103561) baseStart_3103561 baseEnd_3103561 := by
    simpa [prefixWord, tailWord_3103561, baseEnd_3103561] using wordTrace_append hprefix tailTrace_3103561
  have hstable : (prefixWord ++ tailWord_3103561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103561).length < 2 ^ (prefixWord ++ tailWord_3103561).sum := by decide
  have hdescent : baseEnd_3103561 < baseStart_3103561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103610 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_3103610 : Nat := 118140960795 + 3103610 * 2 ^ 59
def prefixEnd_3103610 : Nat := 4983230072969 + 3 ^ 40 * 3103610 * 2
def baseEnd_3103610 : Nat := 1062429129400471563534509

theorem tailTrace_3103610 : CollatzResearch.WordTrace tailWord_3103610 prefixEnd_3103610 1062429129400471563534509 := by
  unfold tailWord_3103610
  simp only [CollatzResearch.WordTrace]
  refine ⟨28299489071539624808331071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75465304190772332822216189 28299489071539624808331071)
  ·
    refine ⟨42449233607309437212496607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28299489071539624808331071 42449233607309437212496607)
    ·
      refine ⟨63673850410964155818744911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42449233607309437212496607 63673850410964155818744911)
      ·
        refine ⟨95510775616446233728117367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63673850410964155818744911 95510775616446233728117367)
        ·
          refine ⟨143266163424669350592176051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95510775616446233728117367 143266163424669350592176051)
          ·
            refine ⟨214899245137004025888264077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143266163424669350592176051 214899245137004025888264077)
            ·
              refine ⟨80587216926376509708099029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214899245137004025888264077 80587216926376509708099029)
              ·
                refine ⟨1888762896711949446283571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80587216926376509708099029 1888762896711949446283571)
                ·
                  refine ⟨2833144345067924169425357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888762896711949446283571 2833144345067924169425357)
                  ·
                    refine ⟨1062429129400471563534509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833144345067924169425357 1062429129400471563534509)
                    ·
                      rfl

theorem cell22_3103610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_3103610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103610 prefixEnd_3103610 := by exact prefixLift 3103610
  have htrace : WordTrace (prefixWord ++ tailWord_3103610) baseStart_3103610 baseEnd_3103610 := by
    simpa [prefixWord, tailWord_3103610, baseEnd_3103610] using wordTrace_append hprefix tailTrace_3103610
  have hstable : (prefixWord ++ tailWord_3103610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103610).length < 2 ^ (prefixWord ++ tailWord_3103610).sum := by decide
  have hdescent : baseEnd_3103610 < baseStart_3103610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103618 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3103618 : Nat := 118140960795 + 3103618 * 2 ^ 59
def prefixEnd_3103618 : Nat := 4983230072969 + 3 ^ 40 * 3103618 * 2
def baseEnd_3103618 : Nat := 354143955987987403111495

theorem tailTrace_3103618 : CollatzResearch.WordTrace tailWord_3103618 prefixEnd_3103618 354143955987987403111495 := by
  unfold tailWord_3103618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28299562017532379149903877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75465498713419677733077005 28299562017532379149903877)
  ·
    refine ⟨5306167878287321090606977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28299562017532379149903877 5306167878287321090606977)
    ·
      refine ⟨3979625908715490817955233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5306167878287321090606977 3979625908715490817955233)
      ·
        refine ⟨2984719431536618113466425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979625908715490817955233 2984719431536618113466425)
        ·
          refine ⟨2238539573652463585099819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984719431536618113466425 2238539573652463585099819)
          ·
            refine ⟨3357809360478695377649729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238539573652463585099819 3357809360478695377649729)
            ·
              refine ⟨2518357020359021533237297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3357809360478695377649729 2518357020359021533237297)
              ·
                refine ⟨1888767765269266149927973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518357020359021533237297 1888767765269266149927973)
                ·
                  refine ⟨354143955987987403111495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1888767765269266149927973 354143955987987403111495)
                  ·
                    rfl

theorem cell22_3103618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3103618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103618 prefixEnd_3103618 := by exact prefixLift 3103618
  have htrace : WordTrace (prefixWord ++ tailWord_3103618) baseStart_3103618 baseEnd_3103618 := by
    simpa [prefixWord, tailWord_3103618, baseEnd_3103618] using wordTrace_append hprefix tailTrace_3103618
  have hstable : (prefixWord ++ tailWord_3103618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103618).length < 2 ^ (prefixWord ++ tailWord_3103618).sum := by decide
  have hdescent : baseEnd_3103618 < baseStart_3103618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103623 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 5]
def baseStart_3103623 : Nat := 118140960795 + 3103623 * 2 ^ 59
def prefixEnd_3103623 : Nat := 4983230072969 + 3 ^ 40 * 3103623 * 2
def baseEnd_3103623 : Nat := 354144526522047954319823

theorem tailTrace_3103623 : CollatzResearch.WordTrace tailWord_3103623 prefixEnd_3103623 354144526522047954319823 := by
  unfold tailWord_3103623
  simp only [CollatzResearch.WordTrace]
  refine ⟨113198430435111402453547523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75465620290074268302365015 113198430435111402453547523)
  ·
    refine ⟨169797645652667103680321285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113198430435111402453547523 169797645652667103680321285)
    ·
      refine ⟨31837058559875081940060241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169797645652667103680321285 31837058559875081940060241)
      ·
        refine ⟨23877793919906311455045181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31837058559875081940060241 23877793919906311455045181)
        ·
          refine ⟨8954172719964866795641943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23877793919906311455045181 8954172719964866795641943)
          ·
            refine ⟨13431259079947300193462915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954172719964866795641943 13431259079947300193462915)
            ·
              refine ⟨20146888619920950290194373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13431259079947300193462915 20146888619920950290194373)
              ·
                refine ⟨3777541616235178179411445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20146888619920950290194373 3777541616235178179411445)
                ·
                  refine ⟨354144526522047954319823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3777541616235178179411445 354144526522047954319823)
                  ·
                    rfl

theorem cell22_3103623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 5].length) (baseStart_3103623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103623 prefixEnd_3103623 := by exact prefixLift 3103623
  have htrace : WordTrace (prefixWord ++ tailWord_3103623) baseStart_3103623 baseEnd_3103623 := by
    simpa [prefixWord, tailWord_3103623, baseEnd_3103623] using wordTrace_append hprefix tailTrace_3103623
  have hstable : (prefixWord ++ tailWord_3103623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103623).length < 2 ^ (prefixWord ++ tailWord_3103623).sum := by decide
  have hdescent : baseEnd_3103623 < baseStart_3103623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103627 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 1, 3]
def baseStart_3103627 : Nat := 118140960795 + 3103627 * 2 ^ 59
def prefixEnd_3103627 : Nat := 4983230072969 + 3 ^ 40 * 3103627 * 2
def baseEnd_3103627 : Nat := 1062434948847889185859457

theorem tailTrace_3103627 : CollatzResearch.WordTrace tailWord_3103627 prefixEnd_3103627 1062434948847889185859457 := by
  unfold tailWord_3103627
  simp only [CollatzResearch.WordTrace]
  refine ⟨113198576327096911136693135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75465717551397940757795423 113198576327096911136693135)
  ·
    refine ⟨169797864490645366705039703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113198576327096911136693135 169797864490645366705039703)
    ·
      refine ⟨254696796735968050057559555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169797864490645366705039703 254696796735968050057559555)
      ·
        refine ⟨382045195103952075086339333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254696796735968050057559555 382045195103952075086339333)
        ·
          refine ⟨71633474081991014078688625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382045195103952075086339333 71633474081991014078688625)
          ·
            refine ⟨53725105561493260559016469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71633474081991014078688625 53725105561493260559016469)
            ·
              refine ⟨2518364323194996588703897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53725105561493260559016469 2518364323194996588703897)
              ·
                refine ⟨1888773242396247441527923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518364323194996588703897 1888773242396247441527923)
                ·
                  refine ⟨2833159863594371162291885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888773242396247441527923 2833159863594371162291885)
                  ·
                    refine ⟨1062434948847889185859457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833159863594371162291885 1062434948847889185859457)
                    ·
                      rfl

theorem cell22_3103627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 3].length) (baseStart_3103627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103627 prefixEnd_3103627 := by exact prefixLift 3103627
  have htrace : WordTrace (prefixWord ++ tailWord_3103627) baseStart_3103627 baseEnd_3103627 := by
    simpa [prefixWord, tailWord_3103627, baseEnd_3103627] using wordTrace_append hprefix tailTrace_3103627
  have hstable : (prefixWord ++ tailWord_3103627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103627).length < 2 ^ (prefixWord ++ tailWord_3103627).sum := by decide
  have hdescent : baseEnd_3103627 < baseStart_3103627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103651 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 8]
def baseStart_3103651 : Nat := 118140960795 + 3103651 * 2 ^ 59
def prefixEnd_3103651 : Nat := 4983230072969 + 3 ^ 40 * 3103651 * 2
def baseEnd_3103651 : Nat := 354147721512787041086461

theorem tailTrace_3103651 : CollatzResearch.WordTrace tailWord_3103651 prefixEnd_3103651 354147721512787041086461 := by
  unfold tailWord_3103651
  simp only [CollatzResearch.WordTrace]
  refine ⟨113199451679009963235566807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75466301119339975490377871 113199451679009963235566807)
  ·
    refine ⟨169799177518514944853350211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113199451679009963235566807 169799177518514944853350211)
    ·
      refine ⟨254698766277772417280025317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169799177518514944853350211 254698766277772417280025317)
      ·
        refine ⟨47756018677082328240004747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254698766277772417280025317 47756018677082328240004747)
        ·
          refine ⟨71634028015623492360007121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47756018677082328240004747 71634028015623492360007121)
          ·
            refine ⟨53725521011717619270005341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71634028015623492360007121 53725521011717619270005341)
            ·
              refine ⟨20147070379394107226252003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53725521011717619270005341 20147070379394107226252003)
              ·
                refine ⟨30220605569091160839378005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20147070379394107226252003 30220605569091160839378005)
                ·
                  refine ⟨354147721512787041086461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30220605569091160839378005 354147721512787041086461)
                  ·
                    rfl

theorem cell22_3103651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_3103651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103651 prefixEnd_3103651 := by exact prefixLift 3103651
  have htrace : WordTrace (prefixWord ++ tailWord_3103651) baseStart_3103651 baseEnd_3103651 := by
    simpa [prefixWord, tailWord_3103651, baseEnd_3103651] using wordTrace_append hprefix tailTrace_3103651
  have hstable : (prefixWord ++ tailWord_3103651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103651).length < 2 ^ (prefixWord ++ tailWord_3103651).sum := by decide
  have hdescent : baseEnd_3103651 < baseStart_3103651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103661 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3103661 : Nat := 118140960795 + 3103661 * 2 ^ 59
def prefixEnd_3103661 : Nat := 4983230072969 + 3 ^ 40 * 3103661 * 2
def baseEnd_3103661 : Nat := 1062446587742724430509353

theorem tailTrace_3103661 : CollatzResearch.WordTrace tailWord_3103661 prefixEnd_3103661 1062446587742724430509353 := by
  unfold tailWord_3103661
  simp only [CollatzResearch.WordTrace]
  refine ⟨113199816408973734943430837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75466544272649156628953891 113199816408973734943430837)
  ·
    refine ⟨10612482788341287650946641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113199816408973734943430837 10612482788341287650946641)
    ·
      refine ⟨7959362091255965738209981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10612482788341287650946641 7959362091255965738209981)
      ·
        refine ⟨2984760784220987151828743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7959362091255965738209981 2984760784220987151828743)
        ·
          refine ⟨4477141176331480727743115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984760784220987151828743 4477141176331480727743115)
          ·
            refine ⟨6715711764497221091614673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477141176331480727743115 6715711764497221091614673)
            ·
              refine ⟨5036783823372915818711005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715711764497221091614673 5036783823372915818711005)
              ·
                refine ⟨1888793933764843432016627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5036783823372915818711005 1888793933764843432016627)
                ·
                  refine ⟨2833190900647265148024941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888793933764843432016627 2833190900647265148024941)
                  ·
                    refine ⟨1062446587742724430509353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833190900647265148024941 1062446587742724430509353)
                    ·
                      rfl

theorem cell22_3103661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3103661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103661 prefixEnd_3103661 := by exact prefixLift 3103661
  have htrace : WordTrace (prefixWord ++ tailWord_3103661) baseStart_3103661 baseEnd_3103661 := by
    simpa [prefixWord, tailWord_3103661, baseEnd_3103661] using wordTrace_append hprefix tailTrace_3103661
  have hstable : (prefixWord ++ tailWord_3103661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103661).length < 2 ^ (prefixWord ++ tailWord_3103661).sum := by decide
  have hdescent : baseEnd_3103661 < baseStart_3103661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103683 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 4, 3]
def baseStart_3103683 : Nat := 118140960795 + 3103683 * 2 ^ 59
def prefixEnd_3103683 : Nat := 4983230072969 + 3 ^ 40 * 3103683 * 2
def baseEnd_3103683 : Nat := 1062454118792323706459285

theorem tailTrace_3103683 : CollatzResearch.WordTrace tailWord_3103683 prefixEnd_3103683 1062454118792323706459285 := by
  unfold tailWord_3103683
  simp only [CollatzResearch.WordTrace]
  refine ⟨113200618814894032700731703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75467079209929355133821135 113200618814894032700731703)
  ·
    refine ⟨169800928222341049051097555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113200618814894032700731703 169800928222341049051097555)
    ·
      refine ⟨254701392333511573576646333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169800928222341049051097555 254701392333511573576646333)
      ·
        refine ⟨95513022125066840091242375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254701392333511573576646333 95513022125066840091242375)
        ·
          refine ⟨143269533187600260136863563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95513022125066840091242375 143269533187600260136863563)
          ·
            refine ⟨214904299781400390205295345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143269533187600260136863563 214904299781400390205295345)
            ·
              refine ⟨161178224836050292653971509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214904299781400390205295345 161178224836050292653971509)
              ·
                refine ⟨15110458578379714936309829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161178224836050292653971509 15110458578379714936309829)
                ·
                  refine ⟨2833210983446196550558093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15110458578379714936309829 2833210983446196550558093)
                  ·
                    refine ⟨1062454118792323706459285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833210983446196550558093 1062454118792323706459285)
                    ·
                      rfl

theorem cell22_3103683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 3].length) (baseStart_3103683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103683 prefixEnd_3103683 := by exact prefixLift 3103683
  have htrace : WordTrace (prefixWord ++ tailWord_3103683) baseStart_3103683 baseEnd_3103683 := by
    simpa [prefixWord, tailWord_3103683, baseEnd_3103683] using wordTrace_append hprefix tailTrace_3103683
  have hstable : (prefixWord ++ tailWord_3103683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103683).length < 2 ^ (prefixWord ++ tailWord_3103683).sum := by decide
  have hdescent : baseEnd_3103683 < baseStart_3103683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103696 : List Nat := [2, 1, 1, 1, 1, 2, 3, 11]
def baseStart_3103696 : Nat := 118140960795 + 3103696 * 2 ^ 59
def prefixEnd_3103696 : Nat := 4983230072969 + 3 ^ 40 * 3103696 * 2
def baseEnd_3103696 : Nat := 118050952106444000653805

theorem tailTrace_3103696 : CollatzResearch.WordTrace tailWord_3103696 prefixEnd_3103696 118050952106444000653805 := by
  unfold tailWord_3103696
  simp only [CollatzResearch.WordTrace]
  refine ⟨56600546481923467960477471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75467395309231290613969961 56600546481923467960477471)
  ·
    refine ⟨84900819722885201940716207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56600546481923467960477471 84900819722885201940716207)
    ·
      refine ⟨127351229584327802911074311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84900819722885201940716207 127351229584327802911074311)
      ·
        refine ⟨191026844376491704366611467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127351229584327802911074311 191026844376491704366611467)
        ·
          refine ⟨286540266564737556549917201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191026844376491704366611467 286540266564737556549917201)
          ·
            refine ⟨214905199923553167412437901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286540266564737556549917201 214905199923553167412437901)
            ·
              refine ⟨80589449971332437779664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214905199923553167412437901 80589449971332437779664213)
              ·
                refine ⟨118050952106444000653805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80589449971332437779664213 118050952106444000653805)
                ·
                  rfl

theorem cell22_3103696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_3103696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103696 prefixEnd_3103696 := by exact prefixLift 3103696
  have htrace : WordTrace (prefixWord ++ tailWord_3103696) baseStart_3103696 baseEnd_3103696 := by
    simpa [prefixWord, tailWord_3103696, baseEnd_3103696] using wordTrace_append hprefix tailTrace_3103696
  have hstable : (prefixWord ++ tailWord_3103696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103696).length < 2 ^ (prefixWord ++ tailWord_3103696).sum := by decide
  have hdescent : baseEnd_3103696 < baseStart_3103696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103700 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3103700 : Nat := 118140960795 + 3103700 * 2 ^ 59
def prefixEnd_3103700 : Nat := 4983230072969 + 3 ^ 40 * 3103700 * 2
def baseEnd_3103700 : Nat := 1062459938239741328784233

theorem tailTrace_3103700 : CollatzResearch.WordTrace tailWord_3103700 prefixEnd_3103700 1062459938239741328784233 := by
  unfold tailWord_3103700
  simp only [CollatzResearch.WordTrace]
  refine ⟨56600619427916222302050277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75467492570554963069400369 56600619427916222302050277)
  ·
    refine ⟨10612616142734291681634427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56600619427916222302050277 10612616142734291681634427)
    ·
      refine ⟨15918924214101437522451641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10612616142734291681634427 15918924214101437522451641)
      ·
        refine ⟨11939193160576078141838731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15918924214101437522451641 11939193160576078141838731)
        ·
          refine ⟨17908789740864117212758097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11939193160576078141838731 17908789740864117212758097)
          ·
            refine ⟨13431592305648087909568573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17908789740864117212758097 13431592305648087909568573)
            ·
              refine ⟨5036847114618032966088215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13431592305648087909568573 5036847114618032966088215)
              ·
                refine ⟨7555270671927049449132323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036847114618032966088215 7555270671927049449132323)
                ·
                  refine ⟨11332906007890574173698485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555270671927049449132323 11332906007890574173698485)
                  ·
                    refine ⟨1062459938239741328784233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11332906007890574173698485 1062459938239741328784233)
                    ·
                      rfl

theorem cell22_3103700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3103700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103700 prefixEnd_3103700 := by exact prefixLift 3103700
  have htrace : WordTrace (prefixWord ++ tailWord_3103700) baseStart_3103700 baseEnd_3103700 := by
    simpa [prefixWord, tailWord_3103700, baseEnd_3103700] using wordTrace_append hprefix tailTrace_3103700
  have hstable : (prefixWord ++ tailWord_3103700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103700).length < 2 ^ (prefixWord ++ tailWord_3103700).sum := by decide
  have hdescent : baseEnd_3103700 < baseStart_3103700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103790 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3103790 : Nat := 118140960795 + 3103790 * 2 ^ 59
def prefixEnd_3103790 : Nat := 4983230072969 + 3 ^ 40 * 3103790 * 2
def baseEnd_3103790 : Nat := 1062490747079011094033957

theorem tailTrace_3103790 : CollatzResearch.WordTrace tailWord_3103790 prefixEnd_3103790 1062490747079011094033957 := by
  unfold tailWord_3103790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14150565178188298746859603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75469680950337593316584549 14150565178188298746859603)
  ·
    refine ⟨21225847767282448120289405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14150565178188298746859603 21225847767282448120289405)
    ·
      refine ⟨7959692912730918045108527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21225847767282448120289405 7959692912730918045108527)
      ·
        refine ⟨11939539369096377067662791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959692912730918045108527 11939539369096377067662791)
        ·
          refine ⟨17909309053644565601494187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11939539369096377067662791 17909309053644565601494187)
          ·
            refine ⟨26863963580466848402241281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17909309053644565601494187 26863963580466848402241281)
            ·
              refine ⟨20147972685350136301680961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26863963580466848402241281 20147972685350136301680961)
              ·
                refine ⟨15110979514012602226260721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20147972685350136301680961 15110979514012602226260721)
                ·
                  refine ⟨11333234635509451669695541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15110979514012602226260721 11333234635509451669695541)
                  ·
                    refine ⟨1062490747079011094033957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11333234635509451669695541 1062490747079011094033957)
                    ·
                      rfl

theorem cell22_3103790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3103790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103790 prefixEnd_3103790 := by exact prefixLift 3103790
  have htrace : WordTrace (prefixWord ++ tailWord_3103790) baseStart_3103790 baseEnd_3103790 := by
    simpa [prefixWord, tailWord_3103790, baseEnd_3103790] using wordTrace_append hprefix tailTrace_3103790
  have hstable : (prefixWord ++ tailWord_3103790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103790).length < 2 ^ (prefixWord ++ tailWord_3103790).sum := by decide
  have hdescent : baseEnd_3103790 < baseStart_3103790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103796 : List Nat := [2, 5, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_3103796 : Nat := 118140960795 + 3103796 * 2 ^ 59
def prefixEnd_3103796 : Nat := 4983230072969 + 3 ^ 40 * 3103796 * 2
def baseEnd_3103796 : Nat := 1062492801001629078383939

theorem tailTrace_3103796 : CollatzResearch.WordTrace tailWord_3103796 prefixEnd_3103796 1062492801001629078383939 := by
  unfold tailWord_3103796
  simp only [CollatzResearch.WordTrace]
  refine ⟨56602370131742326499797621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75469826842323101999730161 56602370131742326499797621)
  ·
    refine ⟨5306472199850843109356027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56602370131742326499797621 5306472199850843109356027)
    ·
      refine ⟨7959708299776264664034041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5306472199850843109356027 7959708299776264664034041)
      ·
        refine ⟨5969781224832198498025531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7959708299776264664034041 5969781224832198498025531)
        ·
          refine ⟨8954671837248297747038297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969781224832198498025531 8954671837248297747038297)
          ·
            refine ⟨6716003877936223310278723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8954671837248297747038297 6716003877936223310278723)
            ·
              refine ⟨10074005816904334965418085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716003877936223310278723 10074005816904334965418085)
              ·
                refine ⟨1888876090669562806015891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10074005816904334965418085 1888876090669562806015891)
                ·
                  refine ⟨2833314136004344209023837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888876090669562806015891 2833314136004344209023837)
                  ·
                    refine ⟨1062492801001629078383939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833314136004344209023837 1062492801001629078383939)
                    ·
                      rfl

theorem cell22_3103796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_3103796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103796 prefixEnd_3103796 := by exact prefixLift 3103796
  have htrace : WordTrace (prefixWord ++ tailWord_3103796) baseStart_3103796 baseEnd_3103796 := by
    simpa [prefixWord, tailWord_3103796, baseEnd_3103796] using wordTrace_append hprefix tailTrace_3103796
  have hstable : (prefixWord ++ tailWord_3103796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103796).length < 2 ^ (prefixWord ++ tailWord_3103796).sum := by decide
  have hdescent : baseEnd_3103796 < baseStart_3103796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103805 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_3103805 : Nat := 118140960795 + 3103805 * 2 ^ 59
def prefixEnd_3103805 : Nat := 4983230072969 + 3 ^ 40 * 3103805 * 2
def baseEnd_3103805 : Nat := 1062495881885556054908911

theorem tailTrace_3103805 : CollatzResearch.WordTrace tailWord_3103805 prefixEnd_3103805 1062495881885556054908911 := by
  unfold tailWord_3103805
  simp only [CollatzResearch.WordTrace]
  refine ⟨113205068520452047536672869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75470045680301365024448579 113205068520452047536672869)
  ·
    refine ⟨21225950347584758913126163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113205068520452047536672869 21225950347584758913126163)
    ·
      refine ⟨31838925521377138369689245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21225950347584758913126163 31838925521377138369689245)
      ·
        refine ⟨11939597070516426888633467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31838925521377138369689245 11939597070516426888633467)
        ·
          refine ⟨17909395605774640332950201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11939597070516426888633467 17909395605774640332950201)
          ·
            refine ⟨13432046704330980249712651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17909395605774640332950201 13432046704330980249712651)
            ·
              refine ⟨20148070056496470374568977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13432046704330980249712651 20148070056496470374568977)
              ·
                refine ⟨15111052542372352780926733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20148070056496470374568977 15111052542372352780926733)
                ·
                  refine ⟨5666644703389632292847525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15111052542372352780926733 5666644703389632292847525)
                  ·
                    refine ⟨1062495881885556054908911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5666644703389632292847525 1062495881885556054908911)
                    ·
                      rfl

theorem cell22_3103805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_3103805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103805 prefixEnd_3103805 := by exact prefixLift 3103805
  have htrace : WordTrace (prefixWord ++ tailWord_3103805) baseStart_3103805 baseEnd_3103805 := by
    simpa [prefixWord, tailWord_3103805, baseEnd_3103805] using wordTrace_append hprefix tailTrace_3103805
  have hstable : (prefixWord ++ tailWord_3103805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103805).length < 2 ^ (prefixWord ++ tailWord_3103805).sum := by decide
  have hdescent : baseEnd_3103805 < baseStart_3103805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103869 : List Nat := [1, 4, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_3103869 : Nat := 118140960795 + 3103869 * 2 ^ 59
def prefixEnd_3103869 : Nat := 4983230072969 + 3 ^ 40 * 3103869 * 2
def baseEnd_3103869 : Nat := 1062517790393481221308715

theorem tailTrace_3103869 : CollatzResearch.WordTrace tailWord_3103869 prefixEnd_3103869 1062517790393481221308715 := by
  unfold tailWord_3103869
  simp only [CollatzResearch.WordTrace]
  refine ⟨113207402792220186467002661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75471601861480124311335107 113207402792220186467002661)
  ·
    refine ⟨21226388023541284962562999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113207402792220186467002661 21226388023541284962562999)
    ·
      refine ⟨31839582035311927443844499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21226388023541284962562999 31839582035311927443844499)
      ·
        refine ⟨47759373052967891165766749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31839582035311927443844499 47759373052967891165766749)
        ·
          refine ⟨17909764894862959187162531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47759373052967891165766749 17909764894862959187162531)
          ·
            refine ⟨26864647342294438780743797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17909764894862959187162531 26864647342294438780743797)
            ·
              refine ⟨2518560688340103635694731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26864647342294438780743797 2518560688340103635694731)
              ·
                refine ⟨3777841032510155453542097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518560688340103635694731 3777841032510155453542097)
                ·
                  refine ⟨2833380774382616590156573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3777841032510155453542097 2833380774382616590156573)
                  ·
                    refine ⟨1062517790393481221308715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833380774382616590156573 1062517790393481221308715)
                    ·
                      rfl

theorem cell22_3103869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_3103869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103869 prefixEnd_3103869 := by exact prefixLift 3103869
  have htrace : WordTrace (prefixWord ++ tailWord_3103869) baseStart_3103869 baseEnd_3103869 := by
    simpa [prefixWord, tailWord_3103869, baseEnd_3103869] using wordTrace_append hprefix tailTrace_3103869
  have hstable : (prefixWord ++ tailWord_3103869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103869).length < 2 ^ (prefixWord ++ tailWord_3103869).sum := by decide
  have hdescent : baseEnd_3103869 < baseStart_3103869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103965 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3103965 : Nat := 118140960795 + 3103965 * 2 ^ 59
def prefixEnd_3103965 : Nat := 4983230072969 + 3 ^ 40 * 3103965 * 2
def baseEnd_3103965 : Nat := 1062550653155368970908421

theorem tailTrace_3103965 : CollatzResearch.WordTrace tailWord_3103965 prefixEnd_3103965 1062550653155368970908421 := by
  unfold tailWord_3103965
  simp only [CollatzResearch.WordTrace]
  refine ⟨113210904199872394862497349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75473936133248263241664899 113210904199872394862497349)
  ·
    refine ⟨21227044537476074036718253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113210904199872394862497349 21227044537476074036718253)
    ·
      refine ⟨7960141701553527763769345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21227044537476074036718253 7960141701553527763769345)
      ·
        refine ⟨5970106276165145822827009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7960141701553527763769345 5970106276165145822827009)
        ·
          refine ⟨4477579707123859367120257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5970106276165145822827009 4477579707123859367120257)
          ·
            refine ⟨3358184780342894525340193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477579707123859367120257 3358184780342894525340193)
            ·
              refine ⟨2518638585257170894005145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358184780342894525340193 2518638585257170894005145)
              ·
                refine ⟨1888978938942878170503859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518638585257170894005145 1888978938942878170503859)
                ·
                  refine ⟨2833468408414317255755789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888978938942878170503859 2833468408414317255755789)
                  ·
                    refine ⟨1062550653155368970908421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833468408414317255755789 1062550653155368970908421)
                    ·
                      rfl

theorem cell22_3103965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3103965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103965 prefixEnd_3103965 := by exact prefixLift 3103965
  have htrace : WordTrace (prefixWord ++ tailWord_3103965) baseStart_3103965 baseEnd_3103965 := by
    simpa [prefixWord, tailWord_3103965, baseEnd_3103965] using wordTrace_append hprefix tailTrace_3103965
  have hstable : (prefixWord ++ tailWord_3103965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103965).length < 2 ^ (prefixWord ++ tailWord_3103965).sum := by decide
  have hdescent : baseEnd_3103965 < baseStart_3103965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103985 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3103985 : Nat := 118140960795 + 3103985 * 2 ^ 59
def prefixEnd_3103985 : Nat := 4983230072969 + 3 ^ 40 * 3103985 * 2
def baseEnd_3103985 : Nat := 1062557499564095585408359

theorem tailTrace_3103985 : CollatzResearch.WordTrace tailWord_3103985 prefixEnd_3103985 1062557499564095585408359 := by
  unfold tailWord_3103985
  simp only [CollatzResearch.WordTrace]
  refine ⟨113211633659799938278225409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75474422439866625518816939 113211633659799938278225409)
  ·
    refine ⟨84908725244849953708669057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113211633659799938278225409 84908725244849953708669057)
    ·
      refine ⟨63681543933637465281501793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84908725244849953708669057 63681543933637465281501793)
      ·
        refine ⟨47761157950228098961126345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63681543933637465281501793 47761157950228098961126345)
        ·
          refine ⟨35820868462671074220844759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47761157950228098961126345 35820868462671074220844759)
          ·
            refine ⟨53731302694006611331267139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35820868462671074220844759 53731302694006611331267139)
            ·
              refine ⟨80596954041009916996900709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53731302694006611331267139 80596954041009916996900709)
              ·
                refine ⟨15111928882689359436918883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80596954041009916996900709 15111928882689359436918883)
                ·
                  refine ⟨22667893324034039155378325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15111928882689359436918883 22667893324034039155378325)
                  ·
                    refine ⟨1062557499564095585408359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22667893324034039155378325 1062557499564095585408359)
                    ·
                      rfl

theorem cell22_3103985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3103985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103985 prefixEnd_3103985 := by exact prefixLift 3103985
  have htrace : WordTrace (prefixWord ++ tailWord_3103985) baseStart_3103985 baseEnd_3103985 := by
    simpa [prefixWord, tailWord_3103985, baseEnd_3103985] using wordTrace_append hprefix tailTrace_3103985
  have hstable : (prefixWord ++ tailWord_3103985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103985).length < 2 ^ (prefixWord ++ tailWord_3103985).sum := by decide
  have hdescent : baseEnd_3103985 < baseStart_3103985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3103987 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 1, 5]
def baseStart_3103987 : Nat := 118140960795 + 3103987 * 2 ^ 59
def prefixEnd_3103987 : Nat := 4983230072969 + 3 ^ 40 * 3103987 * 2
def baseEnd_3103987 : Nat := 1062558184204968246858353

theorem tailTrace_3103987 : CollatzResearch.WordTrace tailWord_3103987 prefixEnd_3103987 1062558184204968246858353 := by
  unfold tailWord_3103987
  simp only [CollatzResearch.WordTrace]
  refine ⟨113211706605792692619798215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75474471070528461746532143 113211706605792692619798215)
  ·
    refine ⟨169817559908689038929697323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113211706605792692619798215 169817559908689038929697323)
    ·
      refine ⟨254726339863033558394545985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169817559908689038929697323 254726339863033558394545985)
      ·
        refine ⟨191044754897275168795909489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254726339863033558394545985 191044754897275168795909489)
        ·
          refine ⟨143283566172956376596932117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191044754897275168795909489 143283566172956376596932117)
          ·
            refine ⟨6716417164357330152981193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143283566172956376596932117 6716417164357330152981193)
            ·
              refine ⟨5037312873267997614735895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6716417164357330152981193 5037312873267997614735895)
              ·
                refine ⟨7555969309901996422103843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037312873267997614735895 7555969309901996422103843)
                ·
                  refine ⟨11333953964852994633155765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555969309901996422103843 11333953964852994633155765)
                  ·
                    refine ⟨1062558184204968246858353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11333953964852994633155765 1062558184204968246858353)
                    ·
                      rfl

theorem cell22_3103987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_3103987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3103987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3103987 prefixEnd_3103987 := by exact prefixLift 3103987
  have htrace : WordTrace (prefixWord ++ tailWord_3103987) baseStart_3103987 baseEnd_3103987 := by
    simpa [prefixWord, tailWord_3103987, baseEnd_3103987] using wordTrace_append hprefix tailTrace_3103987
  have hstable : (prefixWord ++ tailWord_3103987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3103987).length < 2 ^ (prefixWord ++ tailWord_3103987).sum := by decide
  have hdescent : baseEnd_3103987 < baseStart_3103987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3103987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104008 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_3104008 : Nat := 118140960795 + 3104008 * 2 ^ 59
def prefixEnd_3104008 : Nat := 4983230072969 + 3 ^ 40 * 3104008 * 2
def baseEnd_3104008 : Nat := 1062565372934131192083289

theorem tailTrace_3104008 : CollatzResearch.WordTrace tailWord_3104008 prefixEnd_3104008 1062565372934131192083289 := by
  unfold tailWord_3104008
  simp only [CollatzResearch.WordTrace]
  refine ⟨56606236269358306603156339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75474981692477742137541785 56606236269358306603156339)
  ·
    refine ⟨84909354404037459904734509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56606236269358306603156339 84909354404037459904734509)
    ·
      refine ⟨31841007901514047464275441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84909354404037459904734509 31841007901514047464275441)
      ·
        refine ⟨23880755926135535598206581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31841007901514047464275441 23880755926135535598206581)
        ·
          refine ⟨2238820868075206462331867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23880755926135535598206581 2238820868075206462331867)
          ·
            refine ⟨3358231302112809693497801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238820868075206462331867 3358231302112809693497801)
            ·
              refine ⟨2518673476584607270123351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358231302112809693497801 2518673476584607270123351)
              ·
                refine ⟨3778010214876910905185027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518673476584607270123351 3778010214876910905185027)
                ·
                  refine ⟨5667015322315366357777541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778010214876910905185027 5667015322315366357777541)
                  ·
                    refine ⟨1062565372934131192083289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5667015322315366357777541 1062565372934131192083289)
                    ·
                      rfl

theorem cell22_3104008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_3104008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104008 prefixEnd_3104008 := by exact prefixLift 3104008
  have htrace : WordTrace (prefixWord ++ tailWord_3104008) baseStart_3104008 baseEnd_3104008 := by
    simpa [prefixWord, tailWord_3104008, baseEnd_3104008] using wordTrace_append hprefix tailTrace_3104008
  have hstable : (prefixWord ++ tailWord_3104008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104008).length < 2 ^ (prefixWord ++ tailWord_3104008).sum := by decide
  have hdescent : baseEnd_3104008 < baseStart_3104008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104049 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_3104049 : Nat := 118140960795 + 3104049 * 2 ^ 59
def prefixEnd_3104049 : Nat := 4983230072969 + 3 ^ 40 * 3104049 * 2
def baseEnd_3104049 : Nat := 1062579408072020751808163

theorem tailTrace_3104049 : CollatzResearch.WordTrace tailWord_3104049 prefixEnd_3104049 1062579408072020751808163 := by
  unfold tailWord_3104049
  simp only [CollatzResearch.WordTrace]
  refine ⟨113213967931568077208555201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75475978621045384805703467 113213967931568077208555201)
  ·
    refine ⟨84910475948676057906416401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113213967931568077208555201 84910475948676057906416401)
    ·
      refine ⟨63682856961507043429812301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84910475948676057906416401 63682856961507043429812301)
      ·
        refine ⟨23881071360565141286179613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63682856961507043429812301 23881071360565141286179613)
        ·
          refine ⟨8955401760211927982317355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23881071360565141286179613 8955401760211927982317355)
          ·
            refine ⟨13433102640317891973476033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8955401760211927982317355 13433102640317891973476033)
            ·
              refine ⟨10074826980238418980107025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13433102640317891973476033 10074826980238418980107025)
              ·
                refine ⟨7556120235178814235080269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10074826980238418980107025 7556120235178814235080269)
                ·
                  refine ⟨2833545088192055338155101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7556120235178814235080269 2833545088192055338155101)
                  ·
                    refine ⟨1062579408072020751808163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833545088192055338155101 1062579408072020751808163)
                    ·
                      rfl

theorem cell22_3104049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_3104049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104049 prefixEnd_3104049 := by exact prefixLift 3104049
  have htrace : WordTrace (prefixWord ++ tailWord_3104049) baseStart_3104049 baseEnd_3104049 := by
    simpa [prefixWord, tailWord_3104049, baseEnd_3104049] using wordTrace_append hprefix tailTrace_3104049
  have hstable : (prefixWord ++ tailWord_3104049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104049).length < 2 ^ (prefixWord ++ tailWord_3104049).sum := by decide
  have hdescent : baseEnd_3104049 < baseStart_3104049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104062 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3104062 : Nat := 118140960795 + 3104062 * 2 ^ 59
def prefixEnd_3104062 : Nat := 4983230072969 + 3 ^ 40 * 3104062 * 2
def baseEnd_3104062 : Nat := 354194619412564350411041

theorem tailTrace_3104062 : CollatzResearch.WordTrace tailWord_3104062 prefixEnd_3104062 354194619412564350411041 := by
  unfold tailWord_3104062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151805260065122553597305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75476294720347320285852293 14151805260065122553597305)
  ·
    refine ⟨10613853945048841915197979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14151805260065122553597305 10613853945048841915197979)
    ·
      refine ⟨15920780917573262872796969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10613853945048841915197979 15920780917573262872796969)
      ·
        refine ⟨11940585688179947154597727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15920780917573262872796969 11940585688179947154597727)
        ·
          refine ⟨17910878532269920731896591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11940585688179947154597727 17910878532269920731896591)
          ·
            refine ⟨26866317798404881097844887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17910878532269920731896591 26866317798404881097844887)
            ·
              refine ⟨40299476697607321646767331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26866317798404881097844887 40299476697607321646767331)
              ·
                refine ⟨60449215046410982470150997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40299476697607321646767331 60449215046410982470150997)
                ·
                  refine ⟨354194619412564350411041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60449215046410982470150997 354194619412564350411041)
                  ·
                    rfl

theorem cell22_3104062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3104062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104062 prefixEnd_3104062 := by exact prefixLift 3104062
  have htrace : WordTrace (prefixWord ++ tailWord_3104062) baseStart_3104062 baseEnd_3104062 := by
    simpa [prefixWord, tailWord_3104062, baseEnd_3104062] using wordTrace_append hprefix tailTrace_3104062
  have hstable : (prefixWord ++ tailWord_3104062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104062).length < 2 ^ (prefixWord ++ tailWord_3104062).sum := by decide
  have hdescent : baseEnd_3104062 < baseStart_3104062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104075 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_3104075 : Nat := 118140960795 + 3104075 * 2 ^ 59
def prefixEnd_3104075 : Nat := 4983230072969 + 3 ^ 40 * 3104075 * 2
def baseEnd_3104075 : Nat := 1062588308403365350658083

theorem tailTrace_3104075 : CollatzResearch.WordTrace tailWord_3104075 prefixEnd_3104075 1062588308403365350658083 := by
  unfold tailWord_3104075
  simp only [CollatzResearch.WordTrace]
  refine ⟨113214916229473883649001679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75476610819649255766001119 113214916229473883649001679)
  ·
    refine ⟨169822374344210825473502519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113214916229473883649001679 169822374344210825473502519)
    ·
      refine ⟨254733561516316238210253779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169822374344210825473502519 254733561516316238210253779)
      ·
        refine ⟨382100342274474357315380669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254733561516316238210253779 382100342274474357315380669)
        ·
          refine ⟨143287628352927883993267751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382100342274474357315380669 143287628352927883993267751)
          ·
            refine ⟨214931442529391825989901627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143287628352927883993267751 214931442529391825989901627)
            ·
              refine ⟨322397163794087738984852441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214931442529391825989901627 322397163794087738984852441)
              ·
                refine ⟨241797872845565804238639331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322397163794087738984852441 241797872845565804238639331)
                ·
                  refine ⟨362696809268348706357958997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241797872845565804238639331 362696809268348706357958997)
                  ·
                    refine ⟨1062588308403365350658083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 362696809268348706357958997 1062588308403365350658083)
                    ·
                      rfl

theorem cell22_3104075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_3104075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104075 prefixEnd_3104075 := by exact prefixLift 3104075
  have htrace : WordTrace (prefixWord ++ tailWord_3104075) baseStart_3104075 baseEnd_3104075 := by
    simpa [prefixWord, tailWord_3104075, baseEnd_3104075] using wordTrace_append hprefix tailTrace_3104075
  have hstable : (prefixWord ++ tailWord_3104075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104075).length < 2 ^ (prefixWord ++ tailWord_3104075).sum := by decide
  have hdescent : baseEnd_3104075 < baseStart_3104075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104096 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_3104096 : Nat := 118140960795 + 3104096 * 2 ^ 59
def prefixEnd_3104096 : Nat := 4983230072969 + 3 ^ 40 * 3104096 * 2
def baseEnd_3104096 : Nat := 354198499044176098627673

theorem tailTrace_3104096 : CollatzResearch.WordTrace tailWord_3104096 prefixEnd_3104096 354198499044176098627673 := by
  unfold tailWord_3104096
  simp only [CollatzResearch.WordTrace]
  refine ⟨56607841081198902117758071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75477121441598536157010761 56607841081198902117758071)
  ·
    refine ⟨84911761621798353176637107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56607841081198902117758071 84911761621798353176637107)
    ·
      refine ⟨127367642432697529764955661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84911761621798353176637107 127367642432697529764955661)
      ·
        refine ⟨47762865912261573661858373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127367642432697529764955661 47762865912261573661858373)
        ·
          refine ⟨8955537358549045061598445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47762865912261573661858373 8955537358549045061598445)
          ·
            refine ⟨3358326509455891898099417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8955537358549045061598445 3358326509455891898099417)
            ·
              refine ⟨2518744882091918923574563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358326509455891898099417 2518744882091918923574563)
              ·
                refine ⟨3778117323137878385361845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518744882091918923574563 3778117323137878385361845)
                ·
                  refine ⟨354198499044176098627673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3778117323137878385361845 354198499044176098627673)
                  ·
                    rfl

theorem cell22_3104096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_3104096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104096 prefixEnd_3104096 := by exact prefixLift 3104096
  have htrace : WordTrace (prefixWord ++ tailWord_3104096) baseStart_3104096 baseEnd_3104096 := by
    simpa [prefixWord, tailWord_3104096, baseEnd_3104096] using wordTrace_append hprefix tailTrace_3104096
  have hstable : (prefixWord ++ tailWord_3104096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104096).length < 2 ^ (prefixWord ++ tailWord_3104096).sum := by decide
  have hdescent : baseEnd_3104096 < baseStart_3104096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104109 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3104109 : Nat := 118140960795 + 3104109 * 2 ^ 59
def prefixEnd_3104109 : Nat := 4983230072969 + 3 ^ 40 * 3104109 * 2
def baseEnd_3104109 : Nat := 1062599947298200595307979

theorem tailTrace_3104109 : CollatzResearch.WordTrace tailWord_3104109 prefixEnd_3104109 1062599947298200595307979 := by
  unfold tailWord_3104109
  simp only [CollatzResearch.WordTrace]
  refine ⟨113216156311350707455739381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75477437540900471637159587 113216156311350707455739381)
  ·
    refine ⟨10614014654189128823975567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113216156311350707455739381 10614014654189128823975567)
    ·
      refine ⟨15921021981283693235963351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10614014654189128823975567 15921021981283693235963351)
      ·
        refine ⟨23881532971925539853945027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15921021981283693235963351 23881532971925539853945027)
        ·
          refine ⟨35822299457888309780917541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23881532971925539853945027 35822299457888309780917541)
          ·
            refine ⟨6716681148354058083922039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35822299457888309780917541 6716681148354058083922039)
            ·
              refine ⟨10075021722531087125883059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716681148354058083922039 10075021722531087125883059)
              ·
                refine ⟨15112532583796630688824589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10075021722531087125883059 15112532583796630688824589)
                ·
                  refine ⟨5667199718923736508309221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15112532583796630688824589 5667199718923736508309221)
                  ·
                    refine ⟨1062599947298200595307979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5667199718923736508309221 1062599947298200595307979)
                    ·
                      rfl

theorem cell22_3104109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3104109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104109 prefixEnd_3104109 := by exact prefixLift 3104109
  have htrace : WordTrace (prefixWord ++ tailWord_3104109) baseStart_3104109 baseEnd_3104109 := by
    simpa [prefixWord, tailWord_3104109, baseEnd_3104109] using wordTrace_append hprefix tailTrace_3104109
  have hstable : (prefixWord ++ tailWord_3104109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104109).length < 2 ^ (prefixWord ++ tailWord_3104109).sum := by decide
  have hdescent : baseEnd_3104109 < baseStart_3104109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104122 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_3104122 : Nat := 118140960795 + 3104122 * 2 ^ 59
def prefixEnd_3104122 : Nat := 4983230072969 + 3 ^ 40 * 3104122 * 2
def baseEnd_3104122 : Nat := 1062604397463872894732939

theorem tailTrace_3104122 : CollatzResearch.WordTrace tailWord_3104122 prefixEnd_3104122 1062604397463872894732939 := by
  unfold tailWord_3104122
  simp only [CollatzResearch.WordTrace]
  refine ⟨28304157615075902668990655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75477753640202407117308413 28304157615075902668990655)
  ·
    refine ⟨42456236422613854003485983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28304157615075902668990655 42456236422613854003485983)
    ·
      refine ⟨63684354633920781005228975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42456236422613854003485983 63684354633920781005228975)
      ·
        refine ⟨95526531950881171507843463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63684354633920781005228975 95526531950881171507843463)
        ·
          refine ⟨143289797926321757261765195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95526531950881171507843463 143289797926321757261765195)
          ·
            refine ⟨214934696889482635892647793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143289797926321757261765195 214934696889482635892647793)
            ·
              refine ⟨161201022667111976919485845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214934696889482635892647793 161201022667111976919485845)
              ·
                refine ⟨7556297937520873918100899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161201022667111976919485845 7556297937520873918100899)
                ·
                  refine ⟨11334446906281310877151349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556297937520873918100899 11334446906281310877151349)
                  ·
                    refine ⟨1062604397463872894732939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11334446906281310877151349 1062604397463872894732939)
                    ·
                      rfl

theorem cell22_3104122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_3104122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104122 prefixEnd_3104122 := by exact prefixLift 3104122
  have htrace : WordTrace (prefixWord ++ tailWord_3104122) baseStart_3104122 baseEnd_3104122 := by
    simpa [prefixWord, tailWord_3104122, baseEnd_3104122] using wordTrace_append hprefix tailTrace_3104122
  have hstable : (prefixWord ++ tailWord_3104122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104122).length < 2 ^ (prefixWord ++ tailWord_3104122).sum := by decide
  have hdescent : baseEnd_3104122 < baseStart_3104122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104124 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_3104124 : Nat := 118140960795 + 3104124 * 2 ^ 59
def prefixEnd_3104124 : Nat := 4983230072969 + 3 ^ 40 * 3104124 * 2
def baseEnd_3104124 : Nat := 354201694034915185394311

theorem tailTrace_3104124 : CollatzResearch.WordTrace tailWord_3104124 prefixEnd_3104124 354201694034915185394311 := by
  unfold tailWord_3104124
  simp only [CollatzResearch.WordTrace]
  refine ⟨56608351703148182508767713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75477802270864243345023617 56608351703148182508767713)
  ·
    refine ⟨42456263777361136881575785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56608351703148182508767713 42456263777361136881575785)
    ·
      refine ⟨31842197833020852661181839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42456263777361136881575785 31842197833020852661181839)
      ·
        refine ⟨47763296749531278991772759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31842197833020852661181839 47763296749531278991772759)
        ·
          refine ⟨71644945124296918487659139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47763296749531278991772759 71644945124296918487659139)
          ·
            refine ⟨107467417686445377731488709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71644945124296918487659139 107467417686445377731488709)
            ·
              refine ⟨20150140816208508324654133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107467417686445377731488709 20150140816208508324654133)
              ·
                refine ⟨1889075701519547655436325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20150140816208508324654133 1889075701519547655436325)
                ·
                  refine ⟨354201694034915185394311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889075701519547655436325 354201694034915185394311)
                  ·
                    rfl

theorem cell22_3104124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_3104124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104124 prefixEnd_3104124 := by exact prefixLift 3104124
  have htrace : WordTrace (prefixWord ++ tailWord_3104124) baseStart_3104124 baseEnd_3104124 := by
    simpa [prefixWord, tailWord_3104124, baseEnd_3104124] using wordTrace_append hprefix tailTrace_3104124
  have hstable : (prefixWord ++ tailWord_3104124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104124).length < 2 ^ (prefixWord ++ tailWord_3104124).sum := by decide
  have hdescent : baseEnd_3104124 < baseStart_3104124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104291 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 1, 5]
def baseStart_3104291 : Nat := 118140960795 + 3104291 * 2 ^ 59
def prefixEnd_3104291 : Nat := 4983230072969 + 3 ^ 40 * 3104291 * 2
def baseEnd_3104291 : Nat := 1062662249617612787257421

theorem tailTrace_3104291 : CollatzResearch.WordTrace tailWord_3104291 prefixEnd_3104291 1062662249617612787257421 := by
  unfold tailWord_3104291
  simp only [CollatzResearch.WordTrace]
  refine ⟨113222794396691352538864727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75481862931127568359243151 113222794396691352538864727)
  ·
    refine ⟨169834191595037028808297091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113222794396691352538864727 169834191595037028808297091)
    ·
      refine ⟨254751287392555543212445637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169834191595037028808297091 254751287392555543212445637)
      ·
        refine ⟨47765866386104164352333557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254751287392555543212445637 47765866386104164352333557)
        ·
          refine ⟨4478049973697265408031271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47765866386104164352333557 4478049973697265408031271)
          ·
            refine ⟨6717074960545898112046907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478049973697265408031271 6717074960545898112046907)
            ·
              refine ⟨10075612440818847168070361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717074960545898112046907 10075612440818847168070361)
              ·
                refine ⟨7556709330614135376052771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075612440818847168070361 7556709330614135376052771)
                ·
                  refine ⟨11335063995921203064079157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556709330614135376052771 11335063995921203064079157)
                  ·
                    refine ⟨1062662249617612787257421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11335063995921203064079157 1062662249617612787257421)
                    ·
                      rfl

theorem cell22_3104291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_3104291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104291 prefixEnd_3104291 := by exact prefixLift 3104291
  have htrace : WordTrace (prefixWord ++ tailWord_3104291) baseStart_3104291 baseEnd_3104291 := by
    simpa [prefixWord, tailWord_3104291, baseEnd_3104291] using wordTrace_append hprefix tailTrace_3104291
  have hstable : (prefixWord ++ tailWord_3104291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104291).length < 2 ^ (prefixWord ++ tailWord_3104291).sum := by decide
  have hdescent : baseEnd_3104291 < baseStart_3104291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104310 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3104310 : Nat := 118140960795 + 3104310 * 2 ^ 59
def prefixEnd_3104310 : Nat := 4983230072969 + 3 ^ 40 * 3104310 * 2
def baseEnd_3104310 : Nat := 354222917901967690344121

theorem tailTrace_3104310 : CollatzResearch.WordTrace tailWord_3104310 prefixEnd_3104310 354222917901967690344121 := by
  unfold tailWord_3104310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076467961476407423987899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75482324922415012522537589 7076467961476407423987899)
  ·
    refine ⟨10614701942214611135981849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076467961476407423987899 10614701942214611135981849)
    ·
      refine ⟨7961026456660958351986387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10614701942214611135981849 7961026456660958351986387)
      ·
        refine ⟨11941539684991437527979581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961026456660958351986387 11941539684991437527979581)
        ·
          refine ⟨4478077381871789072992343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11941539684991437527979581 4478077381871789072992343)
          ·
            refine ⟨6717116072807683609488515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478077381871789072992343 6717116072807683609488515)
            ·
              refine ⟨10075674109211525414232773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717116072807683609488515 10075674109211525414232773)
              ·
                refine ⟨1889188895477161015168645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10075674109211525414232773 1889188895477161015168645)
                ·
                  refine ⟨354222917901967690344121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1889188895477161015168645 354222917901967690344121)
                  ·
                    rfl

theorem cell22_3104310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3104310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104310 prefixEnd_3104310 := by exact prefixLift 3104310
  have htrace : WordTrace (prefixWord ++ tailWord_3104310) baseStart_3104310 baseEnd_3104310 := by
    simpa [prefixWord, tailWord_3104310, baseEnd_3104310] using wordTrace_append hprefix tailTrace_3104310
  have hstable : (prefixWord ++ tailWord_3104310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104310).length < 2 ^ (prefixWord ++ tailWord_3104310).sum := by decide
  have hdescent : baseEnd_3104310 < baseStart_3104310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104334 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3104334 : Nat := 118140960795 + 3104334 * 2 ^ 59
def prefixEnd_3104334 : Nat := 4983230072969 + 3 ^ 40 * 3104334 * 2
def baseEnd_3104334 : Nat := 1062676969396375008432289

theorem tailTrace_3104334 : CollatzResearch.WordTrace tailWord_3104334 prefixEnd_3104334 1062676969396375008432289 := by
  unfold tailWord_3104334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153045341941946360335007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75482908490357047255120037 14153045341941946360335007)
  ·
    refine ⟨21229568012912919540502511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14153045341941946360335007 21229568012912919540502511)
    ·
      refine ⟨31844352019369379310753767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21229568012912919540502511 31844352019369379310753767)
      ·
        refine ⟨47766528029054068966130651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31844352019369379310753767 47766528029054068966130651)
        ·
          refine ⟨71649792043581103449195977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47766528029054068966130651 71649792043581103449195977)
          ·
            refine ⟨53737344032685827586896983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71649792043581103449195977 53737344032685827586896983)
            ·
              refine ⟨80606016049028741380345475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53737344032685827586896983 80606016049028741380345475)
              ·
                refine ⟨120909024073543112070518213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80606016049028741380345475 120909024073543112070518213)
                ·
                  refine ⟨22670442013789333513222165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120909024073543112070518213 22670442013789333513222165)
                  ·
                    refine ⟨1062676969396375008432289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22670442013789333513222165 1062676969396375008432289)
                    ·
                      rfl

theorem cell22_3104334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3104334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104334 prefixEnd_3104334 := by exact prefixLift 3104334
  have htrace : WordTrace (prefixWord ++ tailWord_3104334) baseStart_3104334 baseEnd_3104334 := by
    simpa [prefixWord, tailWord_3104334, baseEnd_3104334] using wordTrace_append hprefix tailTrace_3104334
  have hstable : (prefixWord ++ tailWord_3104334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104334).length < 2 ^ (prefixWord ++ tailWord_3104334).sum := by decide
  have hdescent : baseEnd_3104334 < baseStart_3104334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104336 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_3104336 : Nat := 118140960795 + 3104336 * 2 ^ 59
def prefixEnd_3104336 : Nat := 4983230072969 + 3 ^ 40 * 3104336 * 2
def baseEnd_3104336 : Nat := 1062677654037247669882283

theorem tailTrace_3104336 : CollatzResearch.WordTrace tailWord_3104336 prefixEnd_3104336 1062677654037247669882283 := by
  unfold tailWord_3104336
  simp only [CollatzResearch.WordTrace]
  refine ⟨56612217840764162612126431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75482957121018883482835241 56612217840764162612126431)
  ·
    refine ⟨84918326761146243918189647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56612217840764162612126431 84918326761146243918189647)
    ·
      refine ⟨127377490141719365877284471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84918326761146243918189647 127377490141719365877284471)
      ·
        refine ⟨191066235212579048815926707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127377490141719365877284471 191066235212579048815926707)
        ·
          refine ⟨286599352818868573223890061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191066235212579048815926707 286599352818868573223890061)
          ·
            refine ⟨107474757307075714958958773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286599352818868573223890061 107474757307075714958958773)
            ·
              refine ⟨10075758497538348277402385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107474757307075714958958773 10075758497538348277402385)
              ·
                refine ⟨7556818873153761208051789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075758497538348277402385 7556818873153761208051789)
                ·
                  refine ⟨2833807077432660453019421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7556818873153761208051789 2833807077432660453019421)
                  ·
                    refine ⟨1062677654037247669882283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833807077432660453019421 1062677654037247669882283)
                    ·
                      rfl

theorem cell22_3104336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_3104336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104336 prefixEnd_3104336 := by exact prefixLift 3104336
  have htrace : WordTrace (prefixWord ++ tailWord_3104336) baseStart_3104336 baseEnd_3104336 := by
    simpa [prefixWord, tailWord_3104336, baseEnd_3104336] using wordTrace_append hprefix tailTrace_3104336
  have hstable : (prefixWord ++ tailWord_3104336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104336).length < 2 ^ (prefixWord ++ tailWord_3104336).sum := by decide
  have hdescent : baseEnd_3104336 < baseStart_3104336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3104370 : List Nat := [3, 2, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_3104370 : Nat := 118140960795 + 3104370 * 2 ^ 59
def prefixEnd_3104370 : Nat := 4983230072969 + 3 ^ 40 * 3104370 * 2
def baseEnd_3104370 : Nat := 1062689292932082914532179

theorem tailTrace_3104370 : CollatzResearch.WordTrace tailWord_3104370 prefixEnd_3104370 1062689292932082914532179 := by
  unfold tailWord_3104370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28306418940851287257747641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75483783842270099353993709 28306418940851287257747641)
  ·
    refine ⟨21229814205638465443310731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28306418940851287257747641 21229814205638465443310731)
    ·
      refine ⟨31844721308457698164966097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21229814205638465443310731 31844721308457698164966097)
      ·
        refine ⟨23883540981343273623724573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31844721308457698164966097 23883540981343273623724573)
        ·
          refine ⟨8956327868003727608896715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23883540981343273623724573 8956327868003727608896715)
          ·
            refine ⟨13434491802005591413345073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8956327868003727608896715 13434491802005591413345073)
            ·
              refine ⟨10075868851504193560008805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13434491802005591413345073 10075868851504193560008805)
              ·
                refine ⟨1889225409657036292501651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10075868851504193560008805 1889225409657036292501651)
                ·
                  refine ⟨2833838114485554438752477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889225409657036292501651 2833838114485554438752477)
                  ·
                    refine ⟨1062689292932082914532179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833838114485554438752477 1062689292932082914532179)
                    ·
                      rfl

theorem cell22_3104370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_3104370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3104370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3104370 prefixEnd_3104370 := by exact prefixLift 3104370
  have htrace : WordTrace (prefixWord ++ tailWord_3104370) baseStart_3104370 baseEnd_3104370 := by
    simpa [prefixWord, tailWord_3104370, baseEnd_3104370] using wordTrace_append hprefix tailTrace_3104370
  have hstable : (prefixWord ++ tailWord_3104370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3104370).length < 2 ^ (prefixWord ++ tailWord_3104370).sum := by decide
  have hdescent : baseEnd_3104370 < baseStart_3104370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3104370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
