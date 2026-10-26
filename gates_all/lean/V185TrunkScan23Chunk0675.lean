import V185TrunkScan23Chunk0674

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3991000 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_3991000 : Nat := 118140960795 + 3991000 * 2 ^ 59
def prefixEnd_3991000 : Nat := 4983230072969 + 3 ^ 40 * 3991000 * 2
def baseEnd_3991000 : Nat := 2049301292093990427845731

theorem tailTrace_3991000 : CollatzResearch.WordTrace tailWord_3991000 prefixEnd_3991000 2049301292093990427845731 := by
  unfold tailWord_3991000
  simp only [CollatzResearch.WordTrace]
  refine ⟨72781864270648041689741227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97042485694197388919654969 72781864270648041689741227)
  ·
    refine ⟨109172796405972062534611841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72781864270648041689741227 109172796405972062534611841)
    ·
      refine ⟨81879597304479046900958881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109172796405972062534611841 81879597304479046900958881)
      ·
        refine ⟨61409697978359285175719161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81879597304479046900958881 61409697978359285175719161)
        ·
          refine ⟨46057273483769463881789371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61409697978359285175719161 46057273483769463881789371)
          ·
            refine ⟨69085910225654195822684057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46057273483769463881789371 69085910225654195822684057)
            ·
              refine ⟨51814432669240646867013043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69085910225654195822684057 51814432669240646867013043)
              ·
                refine ⟨77721649003860970300519565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51814432669240646867013043 77721649003860970300519565)
                ·
                  refine ⟨29145618376447863862694837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77721649003860970300519565 29145618376447863862694837)
                  ·
                    refine ⟨2732401722791987237127641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29145618376447863862694837 2732401722791987237127641)
                    ·
                      refine ⟨2049301292093990427845731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732401722791987237127641 2049301292093990427845731)
                      ·
                        rfl

theorem cell23_3991000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_3991000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991000 prefixEnd_3991000 := by exact prefixLift 3991000
  have htrace : WordTrace (prefixWord ++ tailWord_3991000) baseStart_3991000 baseEnd_3991000 := by
    simpa [prefixWord, tailWord_3991000, baseEnd_3991000] using wordTrace_append hprefix tailTrace_3991000
  have hstable : (prefixWord ++ tailWord_3991000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991000).length < 2 ^ (prefixWord ++ tailWord_3991000).sum := by decide
  have hdescent : baseEnd_3991000 < baseStart_3991000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991023 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 3, 6]
def baseStart_3991023 : Nat := 118140960795 + 3991023 * 2 ^ 59
def prefixEnd_3991023 : Nat := 4983230072969 + 3 ^ 40 * 3991023 * 2
def baseEnd_3991023 : Nat := 683104367383014612619375

theorem tailTrace_3991023 : CollatzResearch.WordTrace tailWord_3991023 prefixEnd_3991023 683104367383014612619375 := by
  unfold tailWord_3991023
  simp only [CollatzResearch.WordTrace]
  refine ⟨145564567420212758307569723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97043044946808505538379815 145564567420212758307569723)
  ·
    refine ⟨218346851130319137461354585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145564567420212758307569723 218346851130319137461354585)
    ·
      refine ⟨163760138347739353096015939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218346851130319137461354585 163760138347739353096015939)
      ·
        refine ⟨245640207521609029644023909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163760138347739353096015939 245640207521609029644023909)
        ·
          refine ⟨46057538910301693058254483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245640207521609029644023909 46057538910301693058254483)
          ·
            refine ⟨69086308365452539587381725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46057538910301693058254483 69086308365452539587381725)
            ·
              refine ⟨25907365637044702345268147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69086308365452539587381725 25907365637044702345268147)
              ·
                refine ⟨38861048455567053517902221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25907365637044702345268147 38861048455567053517902221)
                ·
                  refine ⟨14572893170837645069213333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38861048455567053517902221 14572893170837645069213333)
                  ·
                    refine ⟨683104367383014612619375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14572893170837645069213333 683104367383014612619375)
                    ·
                      rfl

theorem cell23_3991023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_3991023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991023 prefixEnd_3991023 := by exact prefixLift 3991023
  have htrace : WordTrace (prefixWord ++ tailWord_3991023) baseStart_3991023 baseEnd_3991023 := by
    simpa [prefixWord, tailWord_3991023, baseEnd_3991023] using wordTrace_append hprefix tailTrace_3991023
  have hstable : (prefixWord ++ tailWord_3991023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991023).length < 2 ^ (prefixWord ++ tailWord_3991023).sum := by decide
  have hdescent : baseEnd_3991023 < baseStart_3991023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991041 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_3991041 : Nat := 118140960795 + 3991041 * 2 ^ 59
def prefixEnd_3991041 : Nat := 4983230072969 + 3 ^ 40 * 3991041 * 2
def baseEnd_3991041 : Nat := 2049322344800824767433043

theorem tailTrace_3991041 : CollatzResearch.WordTrace tailWord_3991041 prefixEnd_3991041 2049322344800824767433043 := by
  unfold tailWord_3991041
  simp only [CollatzResearch.WordTrace]
  refine ⟨145565223934147547381724977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97043482622765031587816651 145565223934147547381724977)
  ·
    refine ⟨109173917950610660536293733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145565223934147547381724977 109173917950610660536293733)
    ·
      refine ⟨20470109615739498850555075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109173917950610660536293733 20470109615739498850555075)
      ·
        refine ⟨30705164423609248275832613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20470109615739498850555075 30705164423609248275832613)
        ·
          refine ⟨5757218329426734051718615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30705164423609248275832613 5757218329426734051718615)
          ·
            refine ⟨8635827494140101077577923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757218329426734051718615 8635827494140101077577923)
            ·
              refine ⟨12953741241210151616366885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8635827494140101077577923 12953741241210151616366885)
              ·
                refine ⟨2428826482726903428068791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12953741241210151616366885 2428826482726903428068791)
                ·
                  refine ⟨3643239724090355142103187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428826482726903428068791 3643239724090355142103187)
                  ·
                    refine ⟨5464859586135532713154781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643239724090355142103187 5464859586135532713154781)
                    ·
                      refine ⟨2049322344800824767433043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5464859586135532713154781 2049322344800824767433043)
                      ·
                        rfl

theorem cell23_3991041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_3991041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991041 prefixEnd_3991041 := by exact prefixLift 3991041
  have htrace : WordTrace (prefixWord ++ tailWord_3991041) baseStart_3991041 baseEnd_3991041 := by
    simpa [prefixWord, tailWord_3991041, baseEnd_3991041] using wordTrace_append hprefix tailTrace_3991041
  have hstable : (prefixWord ++ tailWord_3991041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991041).length < 2 ^ (prefixWord ++ tailWord_3991041).sum := by decide
  have hdescent : baseEnd_3991041 < baseStart_3991041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991043 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_3991043 : Nat := 118140960795 + 3991043 * 2 ^ 59
def prefixEnd_3991043 : Nat := 4983230072969 + 3 ^ 40 * 3991043 * 2
def baseEnd_3991043 : Nat := 2049323371762133759608033

theorem tailTrace_3991043 : CollatzResearch.WordTrace tailWord_3991043 prefixEnd_3991043 2049323371762133759608033 := by
  unfold tailWord_3991043
  simp only [CollatzResearch.WordTrace]
  refine ⟨145565296880140301723297783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97043531253426867815531855 145565296880140301723297783)
  ·
    refine ⟨218347945320210452584946675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145565296880140301723297783 218347945320210452584946675)
    ·
      refine ⟨327521917980315678877420013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218347945320210452584946675 327521917980315678877420013)
      ·
        refine ⟨122820719242618379579032505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327521917980315678877420013 122820719242618379579032505)
        ·
          refine ⟨92115539431963784684274379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122820719242618379579032505 92115539431963784684274379)
          ·
            refine ⟨138173309147945677026411569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92115539431963784684274379 138173309147945677026411569)
            ·
              refine ⟨103629981860959257769808677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138173309147945677026411569 103629981860959257769808677)
              ·
                refine ⟨19430621598929860831839127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103629981860959257769808677 19430621598929860831839127)
                ·
                  refine ⟨29145932398394791247758691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19430621598929860831839127 29145932398394791247758691)
                  ·
                    refine ⟨43718898597592186871638037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29145932398394791247758691 43718898597592186871638037)
                    ·
                      refine ⟨2049323371762133759608033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43718898597592186871638037 2049323371762133759608033)
                      ·
                        rfl

theorem cell23_3991043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_3991043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991043 prefixEnd_3991043 := by exact prefixLift 3991043
  have htrace : WordTrace (prefixWord ++ tailWord_3991043) baseStart_3991043 baseEnd_3991043 := by
    simpa [prefixWord, tailWord_3991043, baseEnd_3991043] using wordTrace_append hprefix tailTrace_3991043
  have hstable : (prefixWord ++ tailWord_3991043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991043).length < 2 ^ (prefixWord ++ tailWord_3991043).sum := by decide
  have hdescent : baseEnd_3991043 < baseStart_3991043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991123 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_3991123 : Nat := 118140960795 + 3991123 * 2 ^ 59
def prefixEnd_3991123 : Nat := 4983230072969 + 3 ^ 40 * 3991123 * 2
def baseEnd_3991123 : Nat := 2049364450214493446607665

theorem tailTrace_3991123 : CollatzResearch.WordTrace tailWord_3991123 prefixEnd_3991123 2049364450214493446607665 := by
  unfold tailWord_3991123
  simp only [CollatzResearch.WordTrace]
  refine ⟨145568214719850475386210023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97045476479900316924140015 145568214719850475386210023)
  ·
    refine ⟨218352322079775713079315035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145568214719850475386210023 218352322079775713079315035)
    ·
      refine ⟨327528483119663569618972553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218352322079775713079315035 327528483119663569618972553)
      ·
        refine ⟨245646362339747677214229415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327528483119663569618972553 245646362339747677214229415)
        ·
          refine ⟨368469543509621515821344123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245646362339747677214229415 368469543509621515821344123)
          ·
            refine ⟨552704315264432273732016185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368469543509621515821344123 552704315264432273732016185)
            ·
              refine ⟨414528236448324205299012139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552704315264432273732016185 414528236448324205299012139)
              ·
                refine ⟨621792354672486307948518209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414528236448324205299012139 621792354672486307948518209)
                ·
                  refine ⟨466344266004364730961388657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 621792354672486307948518209 466344266004364730961388657)
                  ·
                    refine ⟨349758199503273548221041493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 466344266004364730961388657 349758199503273548221041493)
                    ·
                      refine ⟨2049364450214493446607665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 349758199503273548221041493 2049364450214493446607665)
                      ·
                        rfl

theorem cell23_3991123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_3991123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991123 prefixEnd_3991123 := by exact prefixLift 3991123
  have htrace : WordTrace (prefixWord ++ tailWord_3991123) baseStart_3991123 baseEnd_3991123 := by
    simpa [prefixWord, tailWord_3991123, baseEnd_3991123] using wordTrace_append hprefix tailTrace_3991123
  have hstable : (prefixWord ++ tailWord_3991123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991123).length < 2 ^ (prefixWord ++ tailWord_3991123).sum := by decide
  have hdescent : baseEnd_3991123 < baseStart_3991123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991137 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_3991137 : Nat := 118140960795 + 3991137 * 2 ^ 59
def prefixEnd_3991137 : Nat := 4983230072969 + 3 ^ 40 * 3991137 * 2
def baseEnd_3991137 : Nat := 2049371638943656391832601

theorem tailTrace_3991137 : CollatzResearch.WordTrace tailWord_3991137 prefixEnd_3991137 2049371638943656391832601 := by
  unfold tailWord_3991137
  simp only [CollatzResearch.WordTrace]
  refine ⟨145568725341799755777219665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97045816894533170518146443 145568725341799755777219665)
  ·
    refine ⟨109176544006349816832914749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145568725341799755777219665 109176544006349816832914749)
    ·
      refine ⟨40941204002381181312343031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109176544006349816832914749 40941204002381181312343031)
      ·
        refine ⟨61411806003571771968514547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40941204002381181312343031 61411806003571771968514547)
        ·
          refine ⟨92117709005357657952771821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61411806003571771968514547 92117709005357657952771821)
          ·
            refine ⟨34544140877009121732289433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92117709005357657952771821 34544140877009121732289433)
            ·
              refine ⟨25908105657756841299217075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34544140877009121732289433 25908105657756841299217075)
              ·
                refine ⟨38862158486635261948825613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25908105657756841299217075 38862158486635261948825613)
                ·
                  refine ⟨14573309432488223230809605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38862158486635261948825613 14573309432488223230809605)
                  ·
                    refine ⟨2732495518591541855776801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14573309432488223230809605 2732495518591541855776801)
                    ·
                      refine ⟨2049371638943656391832601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732495518591541855776801 2049371638943656391832601)
                      ·
                        rfl

theorem cell23_3991137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_3991137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991137 prefixEnd_3991137 := by exact prefixLift 3991137
  have htrace : WordTrace (prefixWord ++ tailWord_3991137) baseStart_3991137 baseEnd_3991137 := by
    simpa [prefixWord, tailWord_3991137, baseEnd_3991137] using wordTrace_append hprefix tailTrace_3991137
  have hstable : (prefixWord ++ tailWord_3991137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991137).length < 2 ^ (prefixWord ++ tailWord_3991137).sum := by decide
  have hdescent : baseEnd_3991137 < baseStart_3991137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991140 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3991140 : Nat := 118140960795 + 3991140 * 2 ^ 59
def prefixEnd_3991140 : Nat := 4983230072969 + 3 ^ 40 * 3991140 * 2
def baseEnd_3991140 : Nat := 2049373179385619880095087

theorem tailTrace_3991140 : CollatzResearch.WordTrace tailWord_3991140 prefixEnd_3991140 2049373179385619880095087 := by
  unfold tailWord_3991140
  simp only [CollatzResearch.WordTrace]
  refine ⟨72784417380394443644789437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97045889840525924859719249 72784417380394443644789437)
  ·
    refine ⟨27294156517647916366796039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72784417380394443644789437 27294156517647916366796039)
    ·
      refine ⟨40941234776471874550194059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27294156517647916366796039 40941234776471874550194059)
      ·
        refine ⟨61411852164707811825291089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40941234776471874550194059 61411852164707811825291089)
        ·
          refine ⟨46058889123530858868968317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61411852164707811825291089 46058889123530858868968317)
          ·
            refine ⟨17272083421324072075863119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46058889123530858868968317 17272083421324072075863119)
            ·
              refine ⟨25908125131986108113794679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17272083421324072075863119 25908125131986108113794679)
              ·
                refine ⟨38862187697979162170692019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25908125131986108113794679 38862187697979162170692019)
                ·
                  refine ⟨58293281546968743256038029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38862187697979162170692019 58293281546968743256038029)
                  ·
                    refine ⟨21859980580113278721014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58293281546968743256038029 21859980580113278721014261)
                    ·
                      refine ⟨2049373179385619880095087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21859980580113278721014261 2049373179385619880095087)
                      ·
                        rfl

theorem cell23_3991140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3991140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991140 prefixEnd_3991140 := by exact prefixLift 3991140
  have htrace : WordTrace (prefixWord ++ tailWord_3991140) baseStart_3991140 baseEnd_3991140 := by
    simpa [prefixWord, tailWord_3991140, baseEnd_3991140] using wordTrace_append hprefix tailTrace_3991140
  have hstable : (prefixWord ++ tailWord_3991140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991140).length < 2 ^ (prefixWord ++ tailWord_3991140).sum := by decide
  have hdescent : baseEnd_3991140 < baseStart_3991140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991237 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_3991237 : Nat := 118140960795 + 3991237 * 2 ^ 59
def prefixEnd_3991237 : Nat := 4983230072969 + 3 ^ 40 * 3991237 * 2
def baseEnd_3991237 : Nat := 683140995669702000194047

theorem tailTrace_3991237 : CollatzResearch.WordTrace tailWord_3991237 prefixEnd_3991237 683140995669702000194047 := by
  unfold tailWord_3991237
  simp only [CollatzResearch.WordTrace]
  refine ⟨145572372641437472855859965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97048248427624981903906643 145572372641437472855859965)
  ·
    refine ⟨54589639740539052320947487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145572372641437472855859965 54589639740539052320947487)
    ·
      refine ⟨81884459610808578481421231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54589639740539052320947487 81884459610808578481421231)
      ·
        refine ⟨122826689416212867722131847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81884459610808578481421231 122826689416212867722131847)
        ·
          refine ⟨184240034124319301583197771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122826689416212867722131847 184240034124319301583197771)
          ·
            refine ⟨276360051186478952374796657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184240034124319301583197771 276360051186478952374796657)
            ·
              refine ⟨207270038389859214281097493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276360051186478952374796657 207270038389859214281097493)
              ·
                refine ⟨9715783049524650669426445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207270038389859214281097493 9715783049524650669426445)
                ·
                  refine ⟨3643418643571744001034917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9715783049524650669426445 3643418643571744001034917)
                  ·
                    refine ⟨683140995669702000194047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3643418643571744001034917 683140995669702000194047)
                    ·
                      rfl

theorem cell23_3991237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_3991237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991237 prefixEnd_3991237 := by exact prefixLift 3991237
  have htrace : WordTrace (prefixWord ++ tailWord_3991237) baseStart_3991237 baseEnd_3991237 := by
    simpa [prefixWord, tailWord_3991237, baseEnd_3991237] using wordTrace_append hprefix tailTrace_3991237
  have hstable : (prefixWord ++ tailWord_3991237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991237).length < 2 ^ (prefixWord ++ tailWord_3991237).sum := by decide
  have hdescent : baseEnd_3991237 < baseStart_3991237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991244 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3991244 : Nat := 118140960795 + 3991244 * 2 ^ 59
def prefixEnd_3991244 : Nat := 4983230072969 + 3 ^ 40 * 3991244 * 2
def baseEnd_3991244 : Nat := 2049426581373687473194609

theorem tailTrace_3991244 : CollatzResearch.WordTrace tailWord_3991244 prefixEnd_3991244 2049426581373687473194609 := by
  unfold tailWord_3991244
  simp only [CollatzResearch.WordTrace]
  refine ⟨72786313976206056525682393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97048418634941408700909857 72786313976206056525682393)
  ·
    refine ⟨54589735482154542394261795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72786313976206056525682393 54589735482154542394261795)
    ·
      refine ⟨81884603223231813591392693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54589735482154542394261795 81884603223231813591392693)
      ·
        refine ⟨7676681552177982524193065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81884603223231813591392693 7676681552177982524193065)
        ·
          refine ⟨5757511164133486893144799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7676681552177982524193065 5757511164133486893144799)
          ·
            refine ⟨8636266746200230339717199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757511164133486893144799 8636266746200230339717199)
            ·
              refine ⟨12954400119300345509575799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8636266746200230339717199 12954400119300345509575799)
              ·
                refine ⟨19431600178950518264363699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12954400119300345509575799 19431600178950518264363699)
                ·
                  refine ⟨29147400268425777396545549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19431600178950518264363699 29147400268425777396545549)
                  ·
                    refine ⟨10930275100659666523704581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29147400268425777396545549 10930275100659666523704581)
                    ·
                      refine ⟨2049426581373687473194609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10930275100659666523704581 2049426581373687473194609)
                      ·
                        rfl

theorem cell23_3991244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3991244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991244 prefixEnd_3991244 := by exact prefixLift 3991244
  have htrace : WordTrace (prefixWord ++ tailWord_3991244) baseStart_3991244 baseEnd_3991244 := by
    simpa [prefixWord, tailWord_3991244, baseEnd_3991244] using wordTrace_append hprefix tailTrace_3991244
  have hstable : (prefixWord ++ tailWord_3991244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991244).length < 2 ^ (prefixWord ++ tailWord_3991244).sum := by decide
  have hdescent : baseEnd_3991244 < baseStart_3991244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991280 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_3991280 : Nat := 118140960795 + 3991280 * 2 ^ 59
def prefixEnd_3991280 : Nat := 4983230072969 + 3 ^ 40 * 3991280 * 2
def baseEnd_3991280 : Nat := 683148355559083110781481

theorem tailTrace_3991280 : CollatzResearch.WordTrace tailWord_3991280 prefixEnd_3991280 683148355559083110781481 := by
  unfold tailWord_3991280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72786970490140845599837647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97049293986854460799783529 72786970490140845599837647)
  ·
    refine ⟨109180455735211268399756471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72786970490140845599837647 109180455735211268399756471)
    ·
      refine ⟨163770683602816902599634707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109180455735211268399756471 163770683602816902599634707)
      ·
        refine ⟨245656025404225353899452061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163770683602816902599634707 245656025404225353899452061)
        ·
          refine ⟨92121009526584507712294523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245656025404225353899452061 92121009526584507712294523)
          ·
            refine ⟨138181514289876761568441785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92121009526584507712294523 138181514289876761568441785)
            ·
              refine ⟨103636135717407571176331339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138181514289876761568441785 103636135717407571176331339)
              ·
                refine ⟨155454203576111356764497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103636135717407571176331339 155454203576111356764497009)
                ·
                  refine ⟨116590652682083517573372757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155454203576111356764497009 116590652682083517573372757)
                  ·
                    refine ⟨683148355559083110781481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 116590652682083517573372757 683148355559083110781481)
                    ·
                      rfl

theorem cell23_3991280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_3991280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991280 prefixEnd_3991280 := by exact prefixLift 3991280
  have htrace : WordTrace (prefixWord ++ tailWord_3991280) baseStart_3991280 baseEnd_3991280 := by
    simpa [prefixWord, tailWord_3991280, baseEnd_3991280] using wordTrace_append hprefix tailTrace_3991280
  have hstable : (prefixWord ++ tailWord_3991280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991280).length < 2 ^ (prefixWord ++ tailWord_3991280).sum := by decide
  have hdescent : baseEnd_3991280 < baseStart_3991280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991297 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3991297 : Nat := 118140960795 + 3991297 * 2 ^ 59
def prefixEnd_3991297 : Nat := 4983230072969 + 3 ^ 40 * 3991297 * 2
def baseEnd_3991297 : Nat := 683151265282791921943955

theorem tailTrace_3991297 : CollatzResearch.WordTrace tailWord_3991297 prefixEnd_3991297 683151265282791921943955 := by
  unfold tailWord_3991297
  simp only [CollatzResearch.WordTrace]
  refine ⟨145574561021220103103044145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97049707347480068735362763 145574561021220103103044145)
  ·
    refine ⟨109180920765915077327283109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145574561021220103103044145 109180920765915077327283109)
    ·
      refine ⟨20471422643609076998865583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109180920765915077327283109 20471422643609076998865583)
      ·
        refine ⟨30707133965413615498298375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20471422643609076998865583 30707133965413615498298375)
        ·
          refine ⟨46060700948120423247447563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30707133965413615498298375 46060700948120423247447563)
          ·
            refine ⟨69091051422180634871171345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46060700948120423247447563 69091051422180634871171345)
            ·
              refine ⟨51818288566635476153378509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69091051422180634871171345 51818288566635476153378509)
              ·
                refine ⟨19431858212488303557516941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51818288566635476153378509 19431858212488303557516941)
                ·
                  refine ⟨7286946829683113834068853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19431858212488303557516941 7286946829683113834068853)
                  ·
                    refine ⟨683151265282791921943955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7286946829683113834068853 683151265282791921943955)
                    ·
                      rfl

theorem cell23_3991297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3991297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991297 prefixEnd_3991297 := by exact prefixLift 3991297
  have htrace : WordTrace (prefixWord ++ tailWord_3991297) baseStart_3991297 baseEnd_3991297 := by
    simpa [prefixWord, tailWord_3991297, baseEnd_3991297] using wordTrace_append hprefix tailTrace_3991297
  have hstable : (prefixWord ++ tailWord_3991297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991297).length < 2 ^ (prefixWord ++ tailWord_3991297).sum := by decide
  have hdescent : baseEnd_3991297 < baseStart_3991297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991304 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_3991304 : Nat := 118140960795 + 3991304 * 2 ^ 59
def prefixEnd_3991304 : Nat := 4983230072969 + 3 ^ 40 * 3991304 * 2
def baseEnd_3991304 : Nat := 2049457390212957238444333

theorem tailTrace_3991304 : CollatzResearch.WordTrace tailWord_3991304 prefixEnd_3991304 2049457390212957238444333 := by
  unfold tailWord_3991304
  simp only [CollatzResearch.WordTrace]
  refine ⟨72787408166097371649274483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97049877554796495532365977 72787408166097371649274483)
  ·
    refine ⟨109181112249146057473911725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72787408166097371649274483 109181112249146057473911725)
    ·
      refine ⟨40942917093429771552716897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109181112249146057473911725 40942917093429771552716897)
      ·
        refine ⟨30707187820072328664537673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40942917093429771552716897 30707187820072328664537673)
        ·
          refine ⟨23030390865054246498403255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30707187820072328664537673 23030390865054246498403255)
          ·
            refine ⟨34545586297581369747604883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23030390865054246498403255 34545586297581369747604883)
            ·
              refine ⟨51818379446372054621407325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34545586297581369747604883 51818379446372054621407325)
              ·
                refine ⟨19431892292389520483027747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51818379446372054621407325 19431892292389520483027747)
                ·
                  refine ⟨29147838438584280724541621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19431892292389520483027747 29147838438584280724541621)
                  ·
                    refine ⟨2732609853617276317925777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29147838438584280724541621 2732609853617276317925777)
                    ·
                      refine ⟨2049457390212957238444333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732609853617276317925777 2049457390212957238444333)
                      ·
                        rfl

theorem cell23_3991304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_3991304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991304 prefixEnd_3991304 := by exact prefixLift 3991304
  have htrace : WordTrace (prefixWord ++ tailWord_3991304) baseStart_3991304 baseEnd_3991304 := by
    simpa [prefixWord, tailWord_3991304, baseEnd_3991304] using wordTrace_append hprefix tailTrace_3991304
  have hstable : (prefixWord ++ tailWord_3991304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991304).length < 2 ^ (prefixWord ++ tailWord_3991304).sum := by decide
  have hdescent : baseEnd_3991304 < baseStart_3991304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 1, 1, 3]
def baseStart_3991311 : Nat := 118140960795 + 3991311 * 2 ^ 59
def prefixEnd_3991311 : Nat := 4983230072969 + 3 ^ 40 * 3991311 * 2
def baseEnd_3991311 : Nat := 2049460984577538711056801

theorem tailTrace_3991311 : CollatzResearch.WordTrace tailWord_3991311 prefixEnd_3991311 2049460984577538711056801 := by
  unfold tailWord_3991311
  simp only [CollatzResearch.WordTrace]
  refine ⟨145575071643169383494053787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97050047762112922329369191 145575071643169383494053787)
  ·
    refine ⟨218362607464754075241080681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145575071643169383494053787 218362607464754075241080681)
    ·
      refine ⟨163771955598565556430810511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218362607464754075241080681 163771955598565556430810511)
      ·
        refine ⟨245657933397848334646215767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163771955598565556430810511 245657933397848334646215767)
        ·
          refine ⟨368486900096772501969323651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245657933397848334646215767 368486900096772501969323651)
          ·
            refine ⟨552730350145158752953985477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368486900096772501969323651 552730350145158752953985477)
            ·
              refine ⟨103636940652217266178872277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 552730350145158752953985477 103636940652217266178872277)
              ·
                refine ⟨2428990796536342176067319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103636940652217266178872277 2428990796536342176067319)
                ·
                  refine ⟨3643486194804513264100979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2428990796536342176067319 3643486194804513264100979)
                  ·
                    refine ⟨5465229292206769896151469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643486194804513264100979 5465229292206769896151469)
                    ·
                      refine ⟨2049460984577538711056801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5465229292206769896151469 2049460984577538711056801)
                      ·
                        rfl

theorem cell23_3991311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 1, 3].length) (baseStart_3991311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991311 prefixEnd_3991311 := by exact prefixLift 3991311
  have htrace : WordTrace (prefixWord ++ tailWord_3991311) baseStart_3991311 baseEnd_3991311 := by
    simpa [prefixWord, tailWord_3991311, baseEnd_3991311] using wordTrace_append hprefix tailTrace_3991311
  have hstable : (prefixWord ++ tailWord_3991311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991311).length < 2 ^ (prefixWord ++ tailWord_3991311).sum := by decide
  have hdescent : baseEnd_3991311 < baseStart_3991311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991348 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3991348 : Nat := 118140960795 + 3991348 * 2 ^ 59
def prefixEnd_3991348 : Nat := 4983230072969 + 3 ^ 40 * 3991348 * 2
def baseEnd_3991348 : Nat := 683159994453918355431377

theorem tailTrace_3991348 : CollatzResearch.WordTrace tailWord_3991348 prefixEnd_3991348 683159994453918355431377 := by
  unfold tailWord_3991348
  simp only [CollatzResearch.WordTrace]
  refine ⟨72788210572017669406575349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97050947429356892542100465 72788210572017669406575349)
  ·
    refine ⟨6823894741126656506866439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72788210572017669406575349 6823894741126656506866439)
    ·
      refine ⟨10235842111689984760299659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6823894741126656506866439 10235842111689984760299659)
      ·
        refine ⟨15353763167534977140449489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10235842111689984760299659 15353763167534977140449489)
        ·
          refine ⟨11515322375651232855337117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15353763167534977140449489 11515322375651232855337117)
          ·
            refine ⟨4318245890869212320751419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11515322375651232855337117 4318245890869212320751419)
            ·
              refine ⟨6477368836303818481127129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318245890869212320751419 6477368836303818481127129)
              ·
                refine ⟨4858026627227863860845347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6477368836303818481127129 4858026627227863860845347)
                ·
                  refine ⟨7287039940841795791268021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858026627227863860845347 7287039940841795791268021)
                  ·
                    refine ⟨683159994453918355431377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7287039940841795791268021 683159994453918355431377)
                    ·
                      rfl

theorem cell23_3991348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3991348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991348 prefixEnd_3991348 := by exact prefixLift 3991348
  have htrace : WordTrace (prefixWord ++ tailWord_3991348) baseStart_3991348 baseEnd_3991348 := by
    simpa [prefixWord, tailWord_3991348, baseEnd_3991348] using wordTrace_append hprefix tailTrace_3991348
  have hstable : (prefixWord ++ tailWord_3991348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991348).length < 2 ^ (prefixWord ++ tailWord_3991348).sum := by decide
  have hdescent : baseEnd_3991348 < baseStart_3991348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991397 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3991397 : Nat := 118140960795 + 3991397 * 2 ^ 59
def prefixEnd_3991397 : Nat := 4983230072969 + 3 ^ 40 * 3991397 * 2
def baseEnd_3991397 : Nat := 2049505143913825374581405

theorem tailTrace_3991397 : CollatzResearch.WordTrace tailWord_3991397 prefixEnd_3991397 2049505143913825374581405 := by
  unfold tailWord_3991397
  simp only [CollatzResearch.WordTrace]
  refine ⟨145578208320857820181684445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97052138880571880121122963 145578208320857820181684445)
  ·
    refine ⟨54591828120321682568131667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145578208320857820181684445 54591828120321682568131667)
    ·
      refine ⟨81887742180482523852197501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54591828120321682568131667 81887742180482523852197501)
      ·
        refine ⟨30707903317680946444574063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81887742180482523852197501 30707903317680946444574063)
        ·
          refine ⟨46061854976521419666861095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30707903317680946444574063 46061854976521419666861095)
          ·
            refine ⟨69092782464782129500291643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46061854976521419666861095 69092782464782129500291643)
            ·
              refine ⟨103639173697173194250437465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69092782464782129500291643 103639173697173194250437465)
              ·
                refine ⟨77729380272879895687828099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103639173697173194250437465 77729380272879895687828099)
                ·
                  refine ⟨116594070409319843531742149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77729380272879895687828099 116594070409319843531742149)
                  ·
                    refine ⟨21861388201747470662201653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116594070409319843531742149 21861388201747470662201653)
                    ·
                      refine ⟨2049505143913825374581405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21861388201747470662201653 2049505143913825374581405)
                      ·
                        rfl

theorem cell23_3991397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3991397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991397 prefixEnd_3991397 := by exact prefixLift 3991397
  have htrace : WordTrace (prefixWord ++ tailWord_3991397) baseStart_3991397 baseEnd_3991397 := by
    simpa [prefixWord, tailWord_3991397, baseEnd_3991397] using wordTrace_append hprefix tailTrace_3991397
  have hstable : (prefixWord ++ tailWord_3991397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991397).length < 2 ^ (prefixWord ++ tailWord_3991397).sum := by decide
  have hdescent : baseEnd_3991397 < baseStart_3991397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991411 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 1, 3, 2]
def baseStart_3991411 : Nat := 118140960795 + 3991411 * 2 ^ 59
def prefixEnd_3991411 : Nat := 4983230072969 + 3 ^ 40 * 3991411 * 2
def baseEnd_3991411 : Nat := 2049512332642988319806341

theorem tailTrace_3991411 : CollatzResearch.WordTrace tailWord_3991411 prefixEnd_3991411 2049512332642988319806341 := by
  unfold tailWord_3991411
  simp only [CollatzResearch.WordTrace]
  refine ⟨145578718942807100572694087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97052479295204733715129391 145578718942807100572694087)
  ·
    refine ⟨218368078414210650859041131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145578718942807100572694087 218368078414210650859041131)
    ·
      refine ⟨327552117621315976288561697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218368078414210650859041131 327552117621315976288561697)
      ·
        refine ⟨245664088215986982216421273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327552117621315976288561697 245664088215986982216421273)
        ·
          refine ⟨184248066161990236662315955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245664088215986982216421273 184248066161990236662315955)
          ·
            refine ⟨276372099242985354993473933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184248066161990236662315955 276372099242985354993473933)
            ·
              refine ⟨103639537216119508122552725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276372099242985354993473933 103639537216119508122552725)
              ·
                refine ⟨4858103307005601943244659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103639537216119508122552725 4858103307005601943244659)
                ·
                  refine ⟨7287154960508402914866989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858103307005601943244659 7287154960508402914866989)
                  ·
                    refine ⟨2732683110190651093075121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7287154960508402914866989 2732683110190651093075121)
                    ·
                      refine ⟨2049512332642988319806341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732683110190651093075121 2049512332642988319806341)
                      ·
                        rfl

theorem cell23_3991411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 3, 2].length) (baseStart_3991411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991411 prefixEnd_3991411 := by exact prefixLift 3991411
  have htrace : WordTrace (prefixWord ++ tailWord_3991411) baseStart_3991411 baseEnd_3991411 := by
    simpa [prefixWord, tailWord_3991411, baseEnd_3991411] using wordTrace_append hprefix tailTrace_3991411
  have hstable : (prefixWord ++ tailWord_3991411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991411).length < 2 ^ (prefixWord ++ tailWord_3991411).sum := by decide
  have hdescent : baseEnd_3991411 < baseStart_3991411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991417 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_3991417 : Nat := 118140960795 + 3991417 * 2 ^ 59
def prefixEnd_3991417 : Nat := 4983230072969 + 3 ^ 40 * 3991417 * 2
def baseEnd_3991417 : Nat := 683171804508971765443771

theorem tailTrace_3991417 : CollatzResearch.WordTrace tailWord_3991417 prefixEnd_3991417 683171804508971765443771 := by
  unfold tailWord_3991417
  simp only [CollatzResearch.WordTrace]
  refine ⟨145578937780785363597412505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97052625187190242398275003 145578937780785363597412505)
  ·
    refine ⟨109184203335589022698059379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145578937780785363597412505 109184203335589022698059379)
    ·
      refine ⟨163776305003383534047089069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109184203335589022698059379 163776305003383534047089069)
      ·
        refine ⟨61416114376268825267658401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163776305003383534047089069 61416114376268825267658401)
        ·
          refine ⟨46062085782201618950743801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61416114376268825267658401 46062085782201618950743801)
          ·
            refine ⟨34546564336651214213057851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46062085782201618950743801 34546564336651214213057851)
            ·
              refine ⟨51819846504976821319586777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34546564336651214213057851 51819846504976821319586777)
              ·
                refine ⟨38864884878732615989690083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51819846504976821319586777 38864884878732615989690083)
                ·
                  refine ⟨58297327318098923984535125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38864884878732615989690083 58297327318098923984535125)
                  ·
                    refine ⟨683171804508971765443771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58297327318098923984535125 683171804508971765443771)
                    ·
                      rfl

theorem cell23_3991417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_3991417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991417 prefixEnd_3991417 := by exact prefixLift 3991417
  have htrace : WordTrace (prefixWord ++ tailWord_3991417) baseStart_3991417 baseEnd_3991417 := by
    simpa [prefixWord, tailWord_3991417, baseEnd_3991417] using wordTrace_append hprefix tailTrace_3991417
  have hstable : (prefixWord ++ tailWord_3991417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991417).length < 2 ^ (prefixWord ++ tailWord_3991417).sum := by decide
  have hdescent : baseEnd_3991417 < baseStart_3991417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991422 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3991422 : Nat := 118140960795 + 3991422 * 2 ^ 59
def prefixEnd_3991422 : Nat := 4983230072969 + 3 ^ 40 * 3991422 * 2
def baseEnd_3991422 : Nat := 2049517980930187776768791

theorem tailTrace_3991422 : CollatzResearch.WordTrace tailWord_3991422 prefixEnd_3991422 2049517980930187776768791 := by
  unfold tailWord_3991422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18197390018220906181418065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97052746763844832967563013 18197390018220906181418065)
  ·
    refine ⟨13648042513665679636063549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18197390018220906181418065 13648042513665679636063549)
    ·
      refine ⟨5118015942624629863523831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13648042513665679636063549 5118015942624629863523831)
      ·
        refine ⟨7677023913936944795285747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118015942624629863523831 7677023913936944795285747)
        ·
          refine ⟨11515535870905417192928621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677023913936944795285747 11515535870905417192928621)
          ·
            refine ⟨4318325951589531447348233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11515535870905417192928621 4318325951589531447348233)
            ·
              refine ⟨3238744463692148585511175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318325951589531447348233 3238744463692148585511175)
              ·
                refine ⟨4858116695538222878266763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238744463692148585511175 4858116695538222878266763)
                ·
                  refine ⟨7287175043307334317400145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858116695538222878266763 7287175043307334317400145)
                  ·
                    refine ⟨5465381282480500738050109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7287175043307334317400145 5465381282480500738050109)
                    ·
                      refine ⟨2049517980930187776768791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5465381282480500738050109 2049517980930187776768791)
                      ·
                        rfl

theorem cell23_3991422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3991422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991422 prefixEnd_3991422 := by exact prefixLift 3991422
  have htrace : WordTrace (prefixWord ++ tailWord_3991422) baseStart_3991422 baseEnd_3991422 := by
    simpa [prefixWord, tailWord_3991422, baseEnd_3991422] using wordTrace_append hprefix tailTrace_3991422
  have hstable : (prefixWord ++ tailWord_3991422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991422).length < 2 ^ (prefixWord ++ tailWord_3991422).sum := by decide
  have hdescent : baseEnd_3991422 < baseStart_3991422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991474 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_3991474 : Nat := 118140960795 + 3991474 * 2 ^ 59
def prefixEnd_3991474 : Nat := 4983230072969 + 3 ^ 40 * 3991474 * 2
def baseEnd_3991474 : Nat := 2049544681924221573318551

theorem tailTrace_3991474 : CollatzResearch.WordTrace tailWord_3991474 prefixEnd_3991474 2049544681924221573318551 := by
  unfold tailWord_3991474
  simp only [CollatzResearch.WordTrace]
  refine ⟨36395254185394715583059369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97054011161052574888158317 36395254185394715583059369)
  ·
    refine ⟨27296440639046036687294527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36395254185394715583059369 27296440639046036687294527)
    ·
      refine ⟨40944660958569055030941791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27296440639046036687294527 40944660958569055030941791)
      ·
        refine ⟨61416991437853582546412687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40944660958569055030941791 61416991437853582546412687)
        ·
          refine ⟨92125487156780373819619031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61416991437853582546412687 92125487156780373819619031)
          ·
            refine ⟨138188230735170560729428547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92125487156780373819619031 138188230735170560729428547)
            ·
              refine ⟨207282346102755841094142821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138188230735170560729428547 207282346102755841094142821)
              ·
                refine ⟨38865439894266720205151779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207282346102755841094142821 38865439894266720205151779)
                ·
                  refine ⟨58298159841400080307727669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38865439894266720205151779 58298159841400080307727669)
                  ·
                    refine ⟨5465452485131257528849469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58298159841400080307727669 5465452485131257528849469)
                    ·
                      refine ⟨2049544681924221573318551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5465452485131257528849469 2049544681924221573318551)
                      ·
                        rfl

theorem cell23_3991474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_3991474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991474 prefixEnd_3991474 := by exact prefixLift 3991474
  have htrace : WordTrace (prefixWord ++ tailWord_3991474) baseStart_3991474 baseEnd_3991474 := by
    simpa [prefixWord, tailWord_3991474, baseEnd_3991474] using wordTrace_append hprefix tailTrace_3991474
  have hstable : (prefixWord ++ tailWord_3991474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991474).length < 2 ^ (prefixWord ++ tailWord_3991474).sum := by decide
  have hdescent : baseEnd_3991474 < baseStart_3991474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991585 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3991585 : Nat := 118140960795 + 3991585 * 2 ^ 59
def prefixEnd_3991585 : Nat := 4983230072969 + 3 ^ 40 * 3991585 * 2
def baseEnd_3991585 : Nat := 2049601678276870639030541

theorem tailTrace_3991585 : CollatzResearch.WordTrace tailWord_3991585 prefixEnd_3991585 2049601678276870639030541 := by
  unfold tailWord_3991585
  simp only [CollatzResearch.WordTrace]
  refine ⟨145585065244176728289528209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97056710162784485526352139 145585065244176728289528209)
  ·
    refine ⟨109188798933132546217146157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145585065244176728289528209 109188798933132546217146157)
    ·
      refine ⟨40945799599924704831429809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109188798933132546217146157 40945799599924704831429809)
      ·
        refine ⟨30709349699943528623572357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40945799599924704831429809 30709349699943528623572357)
        ·
          refine ⟨5758003068739411616919817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30709349699943528623572357 5758003068739411616919817)
          ·
            refine ⟨4318502301554558712689863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5758003068739411616919817 4318502301554558712689863)
            ·
              refine ⟨6477753452331838069034795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318502301554558712689863 6477753452331838069034795)
              ·
                refine ⟨9716630178497757103552193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6477753452331838069034795 9716630178497757103552193)
                ·
                  refine ⟨7287472633873317827664145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9716630178497757103552193 7287472633873317827664145)
                  ·
                    refine ⟨5465604475404988370748109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7287472633873317827664145 5465604475404988370748109)
                    ·
                      refine ⟨2049601678276870639030541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5465604475404988370748109 2049601678276870639030541)
                      ·
                        rfl

theorem cell23_3991585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3991585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991585 prefixEnd_3991585 := by exact prefixLift 3991585
  have htrace : WordTrace (prefixWord ++ tailWord_3991585) baseStart_3991585 baseEnd_3991585 := by
    simpa [prefixWord, tailWord_3991585, baseEnd_3991585] using wordTrace_append hprefix tailTrace_3991585
  have hstable : (prefixWord ++ tailWord_3991585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991585).length < 2 ^ (prefixWord ++ tailWord_3991585).sum := by decide
  have hdescent : baseEnd_3991585 < baseStart_3991585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991615 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 1, 1, 3]
def baseStart_3991615 : Nat := 118140960795 + 3991615 * 2 ^ 59
def prefixEnd_3991615 : Nat := 4983230072969 + 3 ^ 40 * 3991615 * 2
def baseEnd_3991615 : Nat := 2049617082696505521655403

theorem tailTrace_3991615 : CollatzResearch.WordTrace tailWord_3991615 prefixEnd_3991615 2049617082696505521655403 := by
  unfold tailWord_3991615
  simp only [CollatzResearch.WordTrace]
  refine ⟨145586159434068043413120299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97057439622712028942080199 145586159434068043413120299)
  ·
    refine ⟨218379239151102065119680449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145586159434068043413120299 218379239151102065119680449)
    ·
      refine ⟨163784429363326548839760337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218379239151102065119680449 163784429363326548839760337)
      ·
        refine ⟨122838322022494911629820253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163784429363326548839760337 122838322022494911629820253)
        ·
          refine ⟨46064370758435591861182595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122838322022494911629820253 46064370758435591861182595)
          ·
            refine ⟨69096556137653387791773893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46064370758435591861182595 69096556137653387791773893)
            ·
              refine ⟨12955604275810010210957605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69096556137653387791773893 12955604275810010210957605)
              ·
                refine ⟨2429175801714376914554551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12955604275810010210957605 2429175801714376914554551)
                ·
                  refine ⟨3643763702571565371831827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429175801714376914554551 3643763702571565371831827)
                  ·
                    refine ⟨5465645553857348057747741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3643763702571565371831827 5465645553857348057747741)
                    ·
                      refine ⟨2049617082696505521655403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5465645553857348057747741 2049617082696505521655403)
                      ·
                        rfl

theorem cell23_3991615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_3991615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991615 prefixEnd_3991615 := by exact prefixLift 3991615
  have htrace : WordTrace (prefixWord ++ tailWord_3991615) baseStart_3991615 baseEnd_3991615 := by
    simpa [prefixWord, tailWord_3991615, baseEnd_3991615] using wordTrace_append hprefix tailTrace_3991615
  have hstable : (prefixWord ++ tailWord_3991615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991615).length < 2 ^ (prefixWord ++ tailWord_3991615).sum := by decide
  have hdescent : baseEnd_3991615 < baseStart_3991615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991651 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3991651 : Nat := 118140960795 + 3991651 * 2 ^ 59
def prefixEnd_3991651 : Nat := 4983230072969 + 3 ^ 40 * 3991651 * 2
def baseEnd_3991651 : Nat := 2049635568000067380805237

theorem tailTrace_3991651 : CollatzResearch.WordTrace tailWord_3991651 prefixEnd_3991651 2049635568000067380805237 := by
  unfold tailWord_3991651
  simp only [CollatzResearch.WordTrace]
  refine ⟨145587472461937621561430807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97058314974625081040953871 145587472461937621561430807)
  ·
    refine ⟨218381208692906432342146211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145587472461937621561430807 218381208692906432342146211)
    ·
      refine ⟨327571813039359648513219317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218381208692906432342146211 327571813039359648513219317)
      ·
        refine ⟨30709857472439967048114311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327571813039359648513219317 30709857472439967048114311)
        ·
          refine ⟨46064786208659950572171467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30709857472439967048114311 46064786208659950572171467)
          ·
            refine ⟨69097179312989925858257201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46064786208659950572171467 69097179312989925858257201)
            ·
              refine ⟨51822884484742444393692901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69097179312989925858257201 51822884484742444393692901)
              ·
                refine ⟨9716790840889208323817419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51822884484742444393692901 9716790840889208323817419)
                ·
                  refine ⟨14575186261333812485726129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9716790840889208323817419 14575186261333812485726129)
                  ·
                    refine ⟨10931389696000359364294597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14575186261333812485726129 10931389696000359364294597)
                    ·
                      refine ⟨2049635568000067380805237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10931389696000359364294597 2049635568000067380805237)
                      ·
                        rfl

theorem cell23_3991651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3991651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991651 prefixEnd_3991651 := by exact prefixLift 3991651
  have htrace : WordTrace (prefixWord ++ tailWord_3991651) baseStart_3991651 baseEnd_3991651 := by
    simpa [prefixWord, tailWord_3991651, baseEnd_3991651] using wordTrace_append hprefix tailTrace_3991651
  have hstable : (prefixWord ++ tailWord_3991651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991651).length < 2 ^ (prefixWord ++ tailWord_3991651).sum := by decide
  have hdescent : baseEnd_3991651 < baseStart_3991651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991766 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3991766 : Nat := 118140960795 + 3991766 * 2 ^ 59
def prefixEnd_3991766 : Nat := 4983230072969 + 3 ^ 40 * 3991766 * 2
def baseEnd_3991766 : Nat := 2049694618275334430867209

theorem tailTrace_3991766 : CollatzResearch.WordTrace tailWord_3991766 prefixEnd_3991766 2049694618275334430867209 := by
  unfold tailWord_3991766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099479178532562262616697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97061111237680664134578101 9099479178532562262616697)
  ·
    refine ⟨6824609383899421696962523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9099479178532562262616697 6824609383899421696962523)
    ·
      refine ⟨10236914075849132545443785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6824609383899421696962523 10236914075849132545443785)
      ·
        refine ⟨7677685556886849409082839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10236914075849132545443785 7677685556886849409082839)
        ·
          refine ⟨11516528335330274113624259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7677685556886849409082839 11516528335330274113624259)
          ·
            refine ⟨17274792502995411170436389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11516528335330274113624259 17274792502995411170436389)
            ·
              refine ⟨3239023594311639594456823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17274792502995411170436389 3239023594311639594456823)
              ·
                refine ⟨4858535391467459391685235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239023594311639594456823 4858535391467459391685235)
                ·
                  refine ⟨7287803087201189087527853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858535391467459391685235 7287803087201189087527853)
                  ·
                    refine ⟨2732926157700445907822945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7287803087201189087527853 2732926157700445907822945)
                    ·
                      refine ⟨2049694618275334430867209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732926157700445907822945 2049694618275334430867209)
                      ·
                        rfl

theorem cell23_3991766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3991766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991766 prefixEnd_3991766 := by exact prefixLift 3991766
  have htrace : WordTrace (prefixWord ++ tailWord_3991766) baseStart_3991766 baseEnd_3991766 := by
    simpa [prefixWord, tailWord_3991766, baseEnd_3991766] using wordTrace_append hprefix tailTrace_3991766
  have hstable : (prefixWord ++ tailWord_3991766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991766).length < 2 ^ (prefixWord ++ tailWord_3991766).sum := by decide
  have hdescent : baseEnd_3991766 < baseStart_3991766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991779 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3991779 : Nat := 118140960795 + 3991779 * 2 ^ 59
def prefixEnd_3991779 : Nat := 4983230072969 + 3 ^ 40 * 3991779 * 2
def baseEnd_3991779 : Nat := 2049701293523842880004649

theorem tailTrace_3991779 : CollatzResearch.WordTrace tailWord_3991779 prefixEnd_3991779 2049701293523842880004649 := by
  unfold tailWord_3991779
  simp only [CollatzResearch.WordTrace]
  refine ⟨145592141005473899422090391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97061427336982599614726927 145592141005473899422090391)
  ·
    refine ⟨218388211508210849133135587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145592141005473899422090391 218388211508210849133135587)
    ·
      refine ⟨327582317262316273699703381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218388211508210849133135587 327582317262316273699703381)
      ·
        refine ⟨3838855280417768832418399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 327582317262316273699703381 3838855280417768832418399)
        ·
          refine ⟨5758282920626653248627599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838855280417768832418399 5758282920626653248627599)
          ·
            refine ⟨8637424380939979872941399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5758282920626653248627599 8637424380939979872941399)
            ·
              refine ⟨12956136571409969809412099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8637424380939979872941399 12956136571409969809412099)
              ·
                refine ⟨19434204857114954714118149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12956136571409969809412099 19434204857114954714118149)
                ·
                  refine ⟨3643913410709054008897153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19434204857114954714118149 3643913410709054008897153)
                  ·
                    refine ⟨2732935058031790506672865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3643913410709054008897153 2732935058031790506672865)
                    ·
                      refine ⟨2049701293523842880004649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732935058031790506672865 2049701293523842880004649)
                      ·
                        rfl

theorem cell23_3991779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3991779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991779 prefixEnd_3991779 := by exact prefixLift 3991779
  have htrace : WordTrace (prefixWord ++ tailWord_3991779) baseStart_3991779 baseEnd_3991779 := by
    simpa [prefixWord, tailWord_3991779, baseEnd_3991779] using wordTrace_append hprefix tailTrace_3991779
  have hstable : (prefixWord ++ tailWord_3991779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991779).length < 2 ^ (prefixWord ++ tailWord_3991779).sum := by decide
  have hdescent : baseEnd_3991779 < baseStart_3991779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991798 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3991798 : Nat := 118140960795 + 3991798 * 2 ^ 59
def prefixEnd_3991798 : Nat := 4983230072969 + 3 ^ 40 * 3991798 * 2
def baseEnd_3991798 : Nat := 683237016552092768555687

theorem tailTrace_3991798 : CollatzResearch.WordTrace tailWord_3991798 prefixEnd_3991798 683237016552092768555687 := by
  unfold tailWord_3991798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9099552124525316604189503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97061889328270043778021365 9099552124525316604189503)
  ·
    refine ⟨13649328186787974906284255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9099552124525316604189503 13649328186787974906284255)
    ·
      refine ⟨20473992280181962359426383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13649328186787974906284255 20473992280181962359426383)
      ·
        refine ⟨30710988420272943539139575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20473992280181962359426383 30710988420272943539139575)
        ·
          refine ⟨46066482630409415308709363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30710988420272943539139575 46066482630409415308709363)
          ·
            refine ⟨69099723945614122963064045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46066482630409415308709363 69099723945614122963064045)
            ·
              refine ⟨25912396479605296111149017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69099723945614122963064045 25912396479605296111149017)
              ·
                refine ⟨19434297359703972083361763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25912396479605296111149017 19434297359703972083361763)
                ·
                  refine ⟨29151446039555958125042645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19434297359703972083361763 29151446039555958125042645)
                  ·
                    refine ⟨683237016552092768555687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29151446039555958125042645 683237016552092768555687)
                    ·
                      rfl

theorem cell23_3991798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3991798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991798 prefixEnd_3991798 := by exact prefixLift 3991798
  have htrace : WordTrace (prefixWord ++ tailWord_3991798) baseStart_3991798 baseEnd_3991798 := by
    simpa [prefixWord, tailWord_3991798, baseEnd_3991798] using wordTrace_append hprefix tailTrace_3991798
  have hstable : (prefixWord ++ tailWord_3991798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991798).length < 2 ^ (prefixWord ++ tailWord_3991798).sum := by decide
  have hdescent : baseEnd_3991798 < baseStart_3991798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991811 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 8]
def baseStart_3991811 : Nat := 118140960795 + 3991811 * 2 ^ 59
def prefixEnd_3991811 : Nat := 4983230072969 + 3 ^ 40 * 3991811 * 2
def baseEnd_3991811 : Nat := 683239241634928918268167

theorem tailTrace_3991811 : CollatzResearch.WordTrace tailWord_3991811 prefixEnd_3991811 683239241634928918268167 := by
  unfold tailWord_3991811
  simp only [CollatzResearch.WordTrace]
  refine ⟨145593308141357968887255287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97062205427571979258170191 145593308141357968887255287)
  ·
    refine ⟨218389962212036953330882931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145593308141357968887255287 218389962212036953330882931)
    ·
      refine ⟨327584943318055429996324397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218389962212036953330882931 327584943318055429996324397)
      ·
        refine ⟨122844353744270786248621649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327584943318055429996324397 122844353744270786248621649)
        ·
          refine ⟨92133265308203089686466237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122844353744270786248621649 92133265308203089686466237)
          ·
            refine ⟨34549974490576158632424839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92133265308203089686466237 34549974490576158632424839)
            ·
              refine ⟨51824961735864237948637259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34549974490576158632424839 51824961735864237948637259)
              ·
                refine ⟨77737442603796356922955889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51824961735864237948637259 77737442603796356922955889)
                ·
                  refine ⟨58303081952847267692216917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77737442603796356922955889 58303081952847267692216917)
                  ·
                    refine ⟨683239241634928918268167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58303081952847267692216917 683239241634928918268167)
                    ·
                      rfl

theorem cell23_3991811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_3991811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991811 prefixEnd_3991811 := by exact prefixLift 3991811
  have htrace : WordTrace (prefixWord ++ tailWord_3991811) baseStart_3991811 baseEnd_3991811 := by
    simpa [prefixWord, tailWord_3991811, baseEnd_3991811] using wordTrace_append hprefix tailTrace_3991811
  have hstable : (prefixWord ++ tailWord_3991811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991811).length < 2 ^ (prefixWord ++ tailWord_3991811).sum := by decide
  have hdescent : baseEnd_3991811 < baseStart_3991811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991818 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_3991818 : Nat := 118140960795 + 3991818 * 2 ^ 59
def prefixEnd_3991818 : Nat := 4983230072969 + 3 ^ 40 * 3991818 * 2
def baseEnd_3991818 : Nat := 2049721319269368227416969

theorem tailTrace_3991818 : CollatzResearch.WordTrace tailWord_3991818 prefixEnd_3991818 2049721319269368227416969 := by
  unfold tailWord_3991818
  simp only [CollatzResearch.WordTrace]
  refine ⟨36398390863083152270690027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97062375634888406055173405 36398390863083152270690027)
  ·
    refine ⟨54597586294624728406035041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36398390863083152270690027 54597586294624728406035041)
    ·
      refine ⟨40948189720968546304526281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54597586294624728406035041 40948189720968546304526281)
      ·
        refine ⟨30711142290726409728394711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40948189720968546304526281 30711142290726409728394711)
        ·
          refine ⟨46066713436089614592592067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30711142290726409728394711 46066713436089614592592067)
          ·
            refine ⟨69100070154134421888888101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46066713436089614592592067 69100070154134421888888101)
            ·
              refine ⟨12956263153900204104166519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69100070154134421888888101 12956263153900204104166519)
              ·
                refine ⟨19434394730850306156249779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12956263153900204104166519 19434394730850306156249779)
                ·
                  refine ⟨29151592096275459234374669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19434394730850306156249779 29151592096275459234374669)
                  ·
                    refine ⟨10931847036103297212890501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29151592096275459234374669 10931847036103297212890501)
                    ·
                      refine ⟨2049721319269368227416969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10931847036103297212890501 2049721319269368227416969)
                      ·
                        rfl

theorem cell23_3991818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_3991818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991818 prefixEnd_3991818 := by exact prefixLift 3991818
  have htrace : WordTrace (prefixWord ++ tailWord_3991818) baseStart_3991818 baseEnd_3991818 := by
    simpa [prefixWord, tailWord_3991818, baseEnd_3991818] using wordTrace_append hprefix tailTrace_3991818
  have hstable : (prefixWord ++ tailWord_3991818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991818).length < 2 ^ (prefixWord ++ tailWord_3991818).sum := by decide
  have hdescent : baseEnd_3991818 < baseStart_3991818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991847 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3991847 : Nat := 118140960795 + 3991847 * 2 ^ 59
def prefixEnd_3991847 : Nat := 4983230072969 + 3 ^ 40 * 3991847 * 2
def baseEnd_3991847 : Nat := 2049736210208348613954337

theorem tailTrace_3991847 : CollatzResearch.WordTrace tailWord_3991847 prefixEnd_3991847 2049736210208348613954337 := by
  unfold tailWord_3991847
  simp only [CollatzResearch.WordTrace]
  refine ⟨145594621169227547035565795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97063080779485031357043863 145594621169227547035565795)
  ·
    refine ⟨218391931753841320553348693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145594621169227547035565795 218391931753841320553348693)
    ·
      refine ⟨2559280450240327975234555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 218391931753841320553348693 2559280450240327975234555)
      ·
        refine ⟨3838920675360491962851833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559280450240327975234555 3838920675360491962851833)
        ·
          refine ⟨2879190506520368972138875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3838920675360491962851833 2879190506520368972138875)
          ·
            refine ⟨4318785759780553458208313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879190506520368972138875 4318785759780553458208313)
            ·
              refine ⟨3239089319835415093656235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318785759780553458208313 3239089319835415093656235)
              ·
                refine ⟨4858633979753122640484353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239089319835415093656235 4858633979753122640484353)
                ·
                  refine ⟨3643975484814841980363265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4858633979753122640484353 3643975484814841980363265)
                  ·
                    refine ⟨2732981613611131485272449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3643975484814841980363265 2732981613611131485272449)
                    ·
                      refine ⟨2049736210208348613954337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2732981613611131485272449 2049736210208348613954337)
                      ·
                        rfl

theorem cell23_3991847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3991847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991847 prefixEnd_3991847 := by exact prefixLift 3991847
  have htrace : WordTrace (prefixWord ++ tailWord_3991847) baseStart_3991847 baseEnd_3991847 := by
    simpa [prefixWord, tailWord_3991847, baseEnd_3991847] using wordTrace_append hprefix tailTrace_3991847
  have hstable : (prefixWord ++ tailWord_3991847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991847).length < 2 ^ (prefixWord ++ tailWord_3991847).sum := by decide
  have hdescent : baseEnd_3991847 < baseStart_3991847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991939 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 1, 5]
def baseStart_3991939 : Nat := 118140960795 + 3991939 * 2 ^ 59
def prefixEnd_3991939 : Nat := 4983230072969 + 3 ^ 40 * 3991939 * 2
def baseEnd_3991939 : Nat := 683261150142854084667971

theorem tailTrace_3991939 : CollatzResearch.WordTrace tailWord_3991939 prefixEnd_3991939 683261150142854084667971 := by
  unfold tailWord_3991939
  simp only [CollatzResearch.WordTrace]
  refine ⟨145597976684894246747914871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97065317789929497831943247 145597976684894246747914871)
  ·
    refine ⟨218396965027341370121872307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145597976684894246747914871 218396965027341370121872307)
    ·
      refine ⟨327595447541012055182808461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218396965027341370121872307 327595447541012055182808461)
      ·
        refine ⟨122848292827879520693553173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327595447541012055182808461 122848292827879520693553173)
        ·
          refine ⟨5758513726306852532510305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122848292827879520693553173 5758513726306852532510305)
          ·
            refine ⟨4318885294730139399382729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5758513726306852532510305 4318885294730139399382729)
            ·
              refine ⟨3239163971047604549537047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4318885294730139399382729 3239163971047604549537047)
              ·
                refine ⟨4858745956571406824305571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239163971047604549537047 4858745956571406824305571)
                ·
                  refine ⟨7288118934857110236458357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4858745956571406824305571 7288118934857110236458357)
                  ·
                    refine ⟨683261150142854084667971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7288118934857110236458357 683261150142854084667971)
                    ·
                      rfl

theorem cell23_3991939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 5].length) (baseStart_3991939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991939 prefixEnd_3991939 := by exact prefixLift 3991939
  have htrace : WordTrace (prefixWord ++ tailWord_3991939) baseStart_3991939 baseEnd_3991939 := by
    simpa [prefixWord, tailWord_3991939, baseEnd_3991939] using wordTrace_append hprefix tailTrace_3991939
  have hstable : (prefixWord ++ tailWord_3991939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991939).length < 2 ^ (prefixWord ++ tailWord_3991939).sum := by decide
  have hdescent : baseEnd_3991939 < baseStart_3991939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991948 : List Nat := [2, 2, 1, 2, 1, 5, 10]
def baseStart_3991948 : Nat := 118140960795 + 3991948 * 2 ^ 59
def prefixEnd_3991948 : Nat := 4983230072969 + 3 ^ 40 * 3991948 * 2
def baseEnd_3991948 : Nat := 25306025577215465664091

theorem tailTrace_3991948 : CollatzResearch.WordTrace tailWord_3991948 prefixEnd_3991948 25306025577215465664091 := by
  unfold tailWord_3991948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72799152470930820642496249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97065536627907760856661665 72799152470930820642496249)
  ·
    refine ⟨54599364353198115481872187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72799152470930820642496249 54599364353198115481872187)
    ·
      refine ⟨81899046529797173222808281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54599364353198115481872187 81899046529797173222808281)
      ·
        refine ⟨61424284897347879917106211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81899046529797173222808281 61424284897347879917106211)
        ·
          refine ⟨92136427346021819875659317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61424284897347879917106211 92136427346021819875659317)
          ·
            refine ⟨8637790063689545613343061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92136427346021819875659317 8637790063689545613343061)
            ·
              refine ⟨25306025577215465664091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8637790063689545613343061 25306025577215465664091)
              ·
                rfl

theorem cell23_3991948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 10].length) (baseStart_3991948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991948 prefixEnd_3991948 := by exact prefixLift 3991948
  have htrace : WordTrace (prefixWord ++ tailWord_3991948) baseStart_3991948 baseEnd_3991948 := by
    simpa [prefixWord, tailWord_3991948, baseEnd_3991948] using wordTrace_append hprefix tailTrace_3991948
  have hstable : (prefixWord ++ tailWord_3991948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991948).length < 2 ^ (prefixWord ++ tailWord_3991948).sum := by decide
  have hdescent : baseEnd_3991948 < baseStart_3991948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991969 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3991969 : Nat := 118140960795 + 3991969 * 2 ^ 59
def prefixEnd_3991969 : Nat := 4983230072969 + 3 ^ 40 * 3991969 * 2
def baseEnd_3991969 : Nat := 683266284949399045542925

theorem tailTrace_3991969 : CollatzResearch.WordTrace tailWord_3991969 prefixEnd_3991969 683266284949399045542925 := by
  unfold tailWord_3991969
  simp only [CollatzResearch.WordTrace]
  refine ⟨145599070874785561871506961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97066047249857041247671307 145599070874785561871506961)
  ·
    refine ⟨109199303156089171403630221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145599070874785561871506961 109199303156089171403630221)
    ·
      refine ⟨40949738683533439276361333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109199303156089171403630221 40949738683533439276361333)
      ·
        refine ⟨3839038001581259932158875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40949738683533439276361333 3839038001581259932158875)
        ·
          refine ⟨5758557002371889898238313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839038001581259932158875 5758557002371889898238313)
          ·
            refine ⟨4318917751778917423678735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5758557002371889898238313 4318917751778917423678735)
            ·
              refine ⟨6478376627668376135518103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318917751778917423678735 6478376627668376135518103)
              ·
                refine ⟨9717564941502564203277155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478376627668376135518103 9717564941502564203277155)
                ·
                  refine ⟨14576347412253846304915733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717564941502564203277155 14576347412253846304915733)
                  ·
                    refine ⟨683266284949399045542925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14576347412253846304915733 683266284949399045542925)
                    ·
                      rfl

theorem cell23_3991969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3991969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991969 prefixEnd_3991969 := by exact prefixLift 3991969
  have htrace : WordTrace (prefixWord ++ tailWord_3991969) baseStart_3991969 baseEnd_3991969 := by
    simpa [prefixWord, tailWord_3991969, baseEnd_3991969] using wordTrace_append hprefix tailTrace_3991969
  have hstable : (prefixWord ++ tailWord_3991969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991969).length < 2 ^ (prefixWord ++ tailWord_3991969).sum := by decide
  have hdescent : baseEnd_3991969 < baseStart_3991969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991976 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_3991976 : Nat := 118140960795 + 3991976 * 2 ^ 59
def prefixEnd_3991976 : Nat := 4983230072969 + 3 ^ 40 * 3991976 * 2
def baseEnd_3991976 : Nat := 2049802449212778609241243

theorem tailTrace_3991976 : CollatzResearch.WordTrace tailWord_3991976 prefixEnd_3991976 2049802449212778609241243 := by
  unfold tailWord_3991976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72799663092880101033505891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97066217457173468044674521 72799663092880101033505891)
  ·
    refine ⟨109199494639320151550258837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72799663092880101033505891 109199494639320151550258837)
    ·
      refine ⟨5118726311218132103918383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109199494639320151550258837 5118726311218132103918383)
      ·
        refine ⟨7678089466827198155877575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5118726311218132103918383 7678089466827198155877575)
        ·
          refine ⟨11517134200240797233816363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7678089466827198155877575 11517134200240797233816363)
          ·
            refine ⟨17275701300361195850724545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11517134200240797233816363 17275701300361195850724545)
            ·
              refine ⟨12956775975270896888043409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17275701300361195850724545 12956775975270896888043409)
              ·
                refine ⟨9717581981453172666032557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12956775975270896888043409 9717581981453172666032557)
                ·
                  refine ⟨3644093243044939749762209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9717581981453172666032557 3644093243044939749762209)
                  ·
                    refine ⟨2733069932283704812321657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644093243044939749762209 2733069932283704812321657)
                    ·
                      refine ⟨2049802449212778609241243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733069932283704812321657 2049802449212778609241243)
                      ·
                        rfl

theorem cell23_3991976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_3991976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991976 prefixEnd_3991976 := by exact prefixLift 3991976
  have htrace : WordTrace (prefixWord ++ tailWord_3991976) baseStart_3991976 baseEnd_3991976 := by
    simpa [prefixWord, tailWord_3991976, baseEnd_3991976] using wordTrace_append hprefix tailTrace_3991976
  have hstable : (prefixWord ++ tailWord_3991976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991976).length < 2 ^ (prefixWord ++ tailWord_3991976).sum := by decide
  have hdescent : baseEnd_3991976 < baseStart_3991976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3991993 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 1, 2, 2]
def baseStart_3991993 : Nat := 118140960795 + 3991993 * 2 ^ 59
def prefixEnd_3991993 : Nat := 4983230072969 + 3 ^ 40 * 3991993 * 2
def baseEnd_3991993 : Nat := 2049811178383905042728665

theorem tailTrace_3991993 : CollatzResearch.WordTrace tailWord_3991993 prefixEnd_3991993 2049811178383905042728665 := by
  unfold tailWord_3991993
  simp only [CollatzResearch.WordTrace]
  refine ⟨145599946226698613970380633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97066630817799075980253755 145599946226698613970380633)
  ·
    refine ⟨109199959670023960477785475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145599946226698613970380633 109199959670023960477785475)
    ·
      refine ⟨163799939505035940716678213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109199959670023960477785475 163799939505035940716678213)
      ·
        refine ⟨30712488657194238884377165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163799939505035940716678213 30712488657194238884377165)
        ·
          refine ⟨11517183246447839581641437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30712488657194238884377165 11517183246447839581641437)
          ·
            refine ⟨4318943717417939843115539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11517183246447839581641437 4318943717417939843115539)
            ·
              refine ⟨6478415576126909764673309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4318943717417939843115539 6478415576126909764673309)
              ·
                refine ⟨2429405841047591161752491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6478415576126909764673309 2429405841047591161752491)
                ·
                  refine ⟨3644108761571386742628737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429405841047591161752491 3644108761571386742628737)
                  ·
                    refine ⟨2733081571178540056971553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644108761571386742628737 2733081571178540056971553)
                    ·
                      refine ⟨2049811178383905042728665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733081571178540056971553 2049811178383905042728665)
                      ·
                        rfl

theorem cell23_3991993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_3991993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3991993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3991993 prefixEnd_3991993 := by exact prefixLift 3991993
  have htrace : WordTrace (prefixWord ++ tailWord_3991993) baseStart_3991993 baseEnd_3991993 := by
    simpa [prefixWord, tailWord_3991993, baseEnd_3991993] using wordTrace_append hprefix tailTrace_3991993
  have hstable : (prefixWord ++ tailWord_3991993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3991993).length < 2 ^ (prefixWord ++ tailWord_3991993).sum := by decide
  have hdescent : baseEnd_3991993 < baseStart_3991993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3991993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992032 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2]
def baseStart_3992032 : Nat := 118140960795 + 3992032 * 2 ^ 59
def prefixEnd_3992032 : Nat := 4983230072969 + 3 ^ 40 * 3992032 * 2
def baseEnd_3992032 : Nat := 2049831204129430390140985

theorem tailTrace_3992032 : CollatzResearch.WordTrace tailWord_3992032 prefixEnd_3992032 2049831204129430390140985 := by
  unfold tailWord_3992032
  simp only [CollatzResearch.WordTrace]
  refine ⟨72800684336778661815525175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97067579115704882420700233 72800684336778661815525175)
  ·
    refine ⟨109201026505167992723287763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72800684336778661815525175 109201026505167992723287763)
    ·
      refine ⟨163801539757751989084931645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109201026505167992723287763 163801539757751989084931645)
      ·
        refine ⟨61425577409156995906849367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163801539757751989084931645 61425577409156995906849367)
        ·
          refine ⟨92138366113735493860274051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61425577409156995906849367 92138366113735493860274051)
          ·
            refine ⟨138207549170603240790411077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92138366113735493860274051 138207549170603240790411077)
            ·
              refine ⟨25913915469488107648202077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138207549170603240790411077 25913915469488107648202077)
              ·
                refine ⟨9717718301058040368075779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25913915469488107648202077 9717718301058040368075779)
                ·
                  refine ⟨14576577451587060552113669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9717718301058040368075779 14576577451587060552113669)
                  ·
                    refine ⟨2733108272172573853521313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14576577451587060552113669 2733108272172573853521313)
                    ·
                      refine ⟨2049831204129430390140985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733108272172573853521313 2049831204129430390140985)
                      ·
                        rfl

theorem cell23_3992032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_3992032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992032 prefixEnd_3992032 := by exact prefixLift 3992032
  have htrace : WordTrace (prefixWord ++ tailWord_3992032) baseStart_3992032 baseEnd_3992032 := by
    simpa [prefixWord, tailWord_3992032, baseEnd_3992032] using wordTrace_append hprefix tailTrace_3992032
  have hstable : (prefixWord ++ tailWord_3992032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992032).length < 2 ^ (prefixWord ++ tailWord_3992032).sum := by decide
  have hdescent : baseEnd_3992032 < baseStart_3992032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992085 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3992085 : Nat := 118140960795 + 3992085 * 2 ^ 59
def prefixEnd_3992085 : Nat := 4983230072969 + 3 ^ 40 * 3992085 * 2
def baseEnd_3992085 : Nat := 683286139534706227592747

theorem tailTrace_3992085 : CollatzResearch.WordTrace tailWord_3992085 prefixEnd_3992085 683286139534706227592747 := by
  unfold tailWord_3992085
  simp only [CollatzResearch.WordTrace]
  refine ⟨145603301742365313682729709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97068867828243542455153139 145603301742365313682729709)
  ·
    refine ⟨54601238153386992631023641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145603301742365313682729709 54601238153386992631023641)
    ·
      refine ⟨40950928615040244473267731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54601238153386992631023641 40950928615040244473267731)
      ·
        refine ⟨61426392922560366709901597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40950928615040244473267731 61426392922560366709901597)
        ·
          refine ⟨23034897345960137516213099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61426392922560366709901597 23034897345960137516213099)
          ·
            refine ⟨34552346018940206274319649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23034897345960137516213099 34552346018940206274319649)
            ·
              refine ⟨25914259514205154705739737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34552346018940206274319649 25914259514205154705739737)
              ·
                refine ⟨19435694635653866029304803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25914259514205154705739737 19435694635653866029304803)
                ·
                  refine ⟨29153541953480799043957205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19435694635653866029304803 29153541953480799043957205)
                  ·
                    refine ⟨683286139534706227592747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29153541953480799043957205 683286139534706227592747)
                    ·
                      rfl

theorem cell23_3992085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3992085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992085 prefixEnd_3992085 := by exact prefixLift 3992085
  have htrace : WordTrace (prefixWord ++ tailWord_3992085) baseStart_3992085 baseEnd_3992085 := by
    simpa [prefixWord, tailWord_3992085, baseEnd_3992085] using wordTrace_append hprefix tailTrace_3992085
  have hstable : (prefixWord ++ tailWord_3992085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992085).length < 2 ^ (prefixWord ++ tailWord_3992085).sum := by decide
  have hdescent : baseEnd_3992085 < baseStart_3992085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992142 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3992142 : Nat := 118140960795 + 3992142 * 2 ^ 59
def prefixEnd_3992142 : Nat := 4983230072969 + 3 ^ 40 * 3992142 * 2
def baseEnd_3992142 : Nat := 2049887687001424959765479

theorem tailTrace_3992142 : CollatzResearch.WordTrace tailWord_3992142 prefixEnd_3992142 2049887687001424959765479 := by
  unfold tailWord_3992142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18200672587894851552194335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97070253802105874945036453 18200672587894851552194335)
  ·
    refine ⟨27301008881842277328291503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18200672587894851552194335 27301008881842277328291503)
    ·
      refine ⟨40951513322763415992437255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27301008881842277328291503 40951513322763415992437255)
      ·
        refine ⟨61427269984145123988655883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40951513322763415992437255 61427269984145123988655883)
        ·
          refine ⟨92140904976217685982983825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61427269984145123988655883 92140904976217685982983825)
          ·
            refine ⟨69105678732163264487237869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92140904976217685982983825 69105678732163264487237869)
            ·
              refine ⟨25914629524561224182714201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69105678732163264487237869 25914629524561224182714201)
              ·
                refine ⟨19435972143420918137035651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25914629524561224182714201 19435972143420918137035651)
                ·
                  refine ⟨29153958215131377205553477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19435972143420918137035651 29153958215131377205553477)
                  ·
                    refine ⟨5466367165337133226041277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29153958215131377205553477 5466367165337133226041277)
                    ·
                      refine ⟨2049887687001424959765479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5466367165337133226041277 2049887687001424959765479)
                      ·
                        rfl

theorem cell23_3992142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3992142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992142 prefixEnd_3992142 := by exact prefixLift 3992142
  have htrace : WordTrace (prefixWord ++ tailWord_3992142) baseStart_3992142 baseEnd_3992142 := by
    simpa [prefixWord, tailWord_3992142, baseEnd_3992142] using wordTrace_append hprefix tailTrace_3992142
  have hstable : (prefixWord ++ tailWord_3992142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992142).length < 2 ^ (prefixWord ++ tailWord_3992142).sum := by decide
  have hdescent : baseEnd_3992142 < baseStart_3992142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992196 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 6]
def baseStart_3992196 : Nat := 118140960795 + 3992196 * 2 ^ 59
def prefixEnd_3992196 : Nat := 4983230072969 + 3 ^ 40 * 3992196 * 2
def baseEnd_3992196 : Nat := 227768379439640860943359

theorem tailTrace_3992196 : CollatzResearch.WordTrace tailWord_3992196 prefixEnd_3992196 227768379439640860943359 := by
  unfold tailWord_3992196
  simp only [CollatzResearch.WordTrace]
  refine ⟨72803675122481589820010221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97071566829975453093346961 72803675122481589820010221)
  ·
    refine ⟨27301378170930596182503833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72803675122481589820010221 27301378170930596182503833)
    ·
      refine ⟨20476033628197947136877875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27301378170930596182503833 20476033628197947136877875)
      ·
        refine ⟨30714050442296920705316813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20476033628197947136877875 30714050442296920705316813)
        ·
          refine ⟨11517768915861345264493805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30714050442296920705316813 11517768915861345264493805)
          ·
            refine ⟨4319163343448004474185177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11517768915861345264493805 4319163343448004474185177)
            ·
              refine ⟨3239372507586003355638883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319163343448004474185177 3239372507586003355638883)
              ·
                refine ⟨4859058761379005033458325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3239372507586003355638883 4859058761379005033458325)
                ·
                  refine ⟨227768379439640860943359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4859058761379005033458325 227768379439640860943359)
                  ·
                    rfl

theorem cell23_3992196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_3992196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992196 prefixEnd_3992196 := by exact prefixLift 3992196
  have htrace : WordTrace (prefixWord ++ tailWord_3992196) baseStart_3992196 baseEnd_3992196 := by
    simpa [prefixWord, tailWord_3992196, baseEnd_3992196] using wordTrace_append hprefix tailTrace_3992196
  have hstable : (prefixWord ++ tailWord_3992196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992196).length < 2 ^ (prefixWord ++ tailWord_3992196).sum := by decide
  have hdescent : baseEnd_3992196 < baseStart_3992196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992199 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_3992199 : Nat := 118140960795 + 3992199 * 2 ^ 59
def prefixEnd_3992199 : Nat := 4983230072969 + 3 ^ 40 * 3992199 * 2
def baseEnd_3992199 : Nat := 2049916955398731236752717

theorem tailTrace_3992199 : CollatzResearch.WordTrace tailWord_3992199 prefixEnd_3992199 2049916955398731236752717 := by
  unfold tailWord_3992199
  simp only [CollatzResearch.WordTrace]
  refine ⟨145607459663952311152379651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97071639775968207434919767 145607459663952311152379651)
  ·
    refine ⟨218411189495928466728569477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145607459663952311152379651 218411189495928466728569477)
    ·
      refine ⟨40952098030486587511606777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218411189495928466728569477 40952098030486587511606777)
      ·
        refine ⟨30714073522864940633705083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40952098030486587511606777 30714073522864940633705083)
        ·
          refine ⟨46071110284297410950557625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30714073522864940633705083 46071110284297410950557625)
          ·
            refine ⟨34553332713223058212918219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46071110284297410950557625 34553332713223058212918219)
            ·
              refine ⟨51829999069834587319377329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34553332713223058212918219 51829999069834587319377329)
              ·
                refine ⟨38872499302375940489532997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51829999069834587319377329 38872499302375940489532997)
                ·
                  refine ⟨7288593619195488841787437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38872499302375940489532997 7288593619195488841787437)
                  ·
                    refine ⟨2733222607198308315670289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7288593619195488841787437 2733222607198308315670289)
                    ·
                      refine ⟨2049916955398731236752717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733222607198308315670289 2049916955398731236752717)
                      ·
                        rfl

theorem cell23_3992199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_3992199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992199 prefixEnd_3992199 := by exact prefixLift 3992199
  have htrace : WordTrace (prefixWord ++ tailWord_3992199) baseStart_3992199 baseEnd_3992199 := by
    simpa [prefixWord, tailWord_3992199, baseEnd_3992199] using wordTrace_append hprefix tailTrace_3992199
  have hstable : (prefixWord ++ tailWord_3992199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992199).length < 2 ^ (prefixWord ++ tailWord_3992199).sum := by decide
  have hdescent : baseEnd_3992199 < baseStart_3992199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992216 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_3992216 : Nat := 118140960795 + 3992216 * 2 ^ 59
def prefixEnd_3992216 : Nat := 4983230072969 + 3 ^ 40 * 3992216 * 2
def baseEnd_3992216 : Nat := 2049925684569857670240139

theorem tailTrace_3992216 : CollatzResearch.WordTrace tailWord_3992216 prefixEnd_3992216 2049925684569857670240139 := by
  unfold tailWord_3992216
  simp only [CollatzResearch.WordTrace]
  refine ⟨72804039852445361527874251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97072053136593815370499001 72804039852445361527874251)
  ·
    refine ⟨109206059778668042291811377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72804039852445361527874251 109206059778668042291811377)
    ·
      refine ⟨81904544834001031718858533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109206059778668042291811377 81904544834001031718858533)
      ·
        refine ⟨15357102156375193447285975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81904544834001031718858533 15357102156375193447285975)
        ·
          refine ⟨23035653234562790170928963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15357102156375193447285975 23035653234562790170928963)
          ·
            refine ⟨34553479851844185256393445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23035653234562790170928963 34553479851844185256393445)
            ·
              refine ⟨6478777472220784735573771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34553479851844185256393445 6478777472220784735573771)
              ·
                refine ⟨9718166208331177103360657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478777472220784735573771 9718166208331177103360657)
                ·
                  refine ⟨7288624656248382827520493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9718166208331177103360657 7288624656248382827520493)
                  ·
                    refine ⟨2733234246093143560320185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7288624656248382827520493 2733234246093143560320185)
                    ·
                      refine ⟨2049925684569857670240139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733234246093143560320185 2049925684569857670240139)
                      ·
                        rfl

theorem cell23_3992216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_3992216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992216 prefixEnd_3992216 := by exact prefixLift 3992216
  have htrace : WordTrace (prefixWord ++ tailWord_3992216) baseStart_3992216 baseEnd_3992216 := by
    simpa [prefixWord, tailWord_3992216, baseEnd_3992216] using wordTrace_append hprefix tailTrace_3992216
  have hstable : (prefixWord ++ tailWord_3992216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992216).length < 2 ^ (prefixWord ++ tailWord_3992216).sum := by decide
  have hdescent : baseEnd_3992216 < baseStart_3992216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992234 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3992234 : Nat := 118140960795 + 3992234 * 2 ^ 59
def prefixEnd_3992234 : Nat := 4983230072969 + 3 ^ 40 * 3992234 * 2
def baseEnd_3992234 : Nat := 683311642407212866605019

theorem tailTrace_3992234 : CollatzResearch.WordTrace tailWord_3992234 prefixEnd_3992234 683311642407212866605019 := by
  unfold tailWord_3992234
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402184054706378032475939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97072490812550341419935837 36402184054706378032475939)
  ·
    refine ⟨54603276082059567048713909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36402184054706378032475939 54603276082059567048713909)
    ·
      refine ⟨5119057132693084410816929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54603276082059567048713909 5119057132693084410816929)
      ·
        refine ⟨3839292849519813308112697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5119057132693084410816929 3839292849519813308112697)
        ·
          refine ⟨2879469637139859981084523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839292849519813308112697 2879469637139859981084523)
          ·
            refine ⟨4319204455709789971626785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879469637139859981084523 4319204455709789971626785)
            ·
              refine ⟨3239403341782342478720089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319204455709789971626785 3239403341782342478720089)
              ·
                refine ⟨2429552506336756859040067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239403341782342478720089 2429552506336756859040067)
                ·
                  refine ⟨3644328759505135288560101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429552506336756859040067 3644328759505135288560101)
                  ·
                    refine ⟨683311642407212866605019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3644328759505135288560101 683311642407212866605019)
                    ·
                      rfl

theorem cell23_3992234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3992234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992234 prefixEnd_3992234 := by exact prefixLift 3992234
  have htrace : WordTrace (prefixWord ++ tailWord_3992234) baseStart_3992234 baseEnd_3992234 := by
    simpa [prefixWord, tailWord_3992234, baseEnd_3992234] using wordTrace_append hprefix tailTrace_3992234
  have hstable : (prefixWord ++ tailWord_3992234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992234).length < 2 ^ (prefixWord ++ tailWord_3992234).sum := by decide
  have hdescent : baseEnd_3992234 < baseStart_3992234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992239 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 2, 4]
def baseStart_3992239 : Nat := 118140960795 + 3992239 * 2 ^ 59
def prefixEnd_3992239 : Nat := 4983230072969 + 3 ^ 40 * 3992239 * 2
def baseEnd_3992239 : Nat := 683312498208303693417511

theorem tailTrace_3992239 : CollatzResearch.WordTrace tailWord_3992239 prefixEnd_3992239 683312498208303693417511 := by
  unfold tailWord_3992239
  simp only [CollatzResearch.WordTrace]
  refine ⟨145608918583807397983835771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97072612389204931989223847 145608918583807397983835771)
  ·
    refine ⟨218413377875711096975753657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145608918583807397983835771 218413377875711096975753657)
    ·
      refine ⟨163810033406783322731815243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218413377875711096975753657 163810033406783322731815243)
      ·
        refine ⟨245715050110174984097722865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163810033406783322731815243 245715050110174984097722865)
        ·
          refine ⟨184286287582631238073292149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245715050110174984097722865 184286287582631238073292149)
          ·
            refine ⟨17276839460871678569371139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184286287582631238073292149 17276839460871678569371139)
            ·
              refine ⟨25915259191307517854056709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17276839460871678569371139 25915259191307517854056709)
              ·
                refine ⟨4859111098370159597635633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25915259191307517854056709 4859111098370159597635633)
                ·
                  refine ⟨3644333323777619698226725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859111098370159597635633 3644333323777619698226725)
                  ·
                    refine ⟨683312498208303693417511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3644333323777619698226725 683312498208303693417511)
                    ·
                      rfl

theorem cell23_3992239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_3992239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992239 prefixEnd_3992239 := by exact prefixLift 3992239
  have htrace : WordTrace (prefixWord ++ tailWord_3992239) baseStart_3992239 baseEnd_3992239 := by
    simpa [prefixWord, tailWord_3992239, baseEnd_3992239] using wordTrace_append hprefix tailTrace_3992239
  have hstable : (prefixWord ++ tailWord_3992239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992239).length < 2 ^ (prefixWord ++ tailWord_3992239).sum := by decide
  have hdescent : baseEnd_3992239 < baseStart_3992239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992242 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3992242 : Nat := 118140960795 + 3992242 * 2 ^ 59
def prefixEnd_3992242 : Nat := 4983230072969 + 3 ^ 40 * 3992242 * 2
def baseEnd_3992242 : Nat := 2049939035066874568515019

theorem tailTrace_3992242 : CollatzResearch.WordTrace tailWord_3992242 prefixEnd_3992242 2049939035066874568515019 := by
  unfold tailWord_3992242
  simp only [CollatzResearch.WordTrace]
  refine ⟨36402257000699132374048745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97072685335197686330796653 36402257000699132374048745)
  ·
    refine ⟨27301692750524349280536559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36402257000699132374048745 27301692750524349280536559)
    ·
      refine ⟨40952539125786523920804839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27301692750524349280536559 40952539125786523920804839)
      ·
        refine ⟨61428808688679785881207259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40952539125786523920804839 61428808688679785881207259)
        ·
          refine ⟨92143213033019678821810889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61428808688679785881207259 92143213033019678821810889)
          ·
            refine ⟨69107409774764759116358167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92143213033019678821810889 69107409774764759116358167)
            ·
              refine ⟨103661114662147138674537251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69107409774764759116358167 103661114662147138674537251)
              ·
                refine ⟨155491671993220708011805877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103661114662147138674537251 155491671993220708011805877)
                ·
                  refine ⟨14577344249364441376106801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155491671993220708011805877 14577344249364441376106801)
                  ·
                    refine ⟨10933008187023331032080101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14577344249364441376106801 10933008187023331032080101)
                    ·
                      refine ⟨2049939035066874568515019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10933008187023331032080101 2049939035066874568515019)
                      ·
                        rfl

theorem cell23_3992242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3992242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992242 prefixEnd_3992242 := by exact prefixLift 3992242
  have htrace : WordTrace (prefixWord ++ tailWord_3992242) baseStart_3992242 baseEnd_3992242 := by
    simpa [prefixWord, tailWord_3992242, baseEnd_3992242] using wordTrace_append hprefix tailTrace_3992242
  have hstable : (prefixWord ++ tailWord_3992242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992242).length < 2 ^ (prefixWord ++ tailWord_3992242).sum := by decide
  have hdescent : baseEnd_3992242 < baseStart_3992242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992279 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_3992279 : Nat := 118140960795 + 3992279 * 2 ^ 59
def prefixEnd_3992279 : Nat := 4983230072969 + 3 ^ 40 * 3992279 * 2
def baseEnd_3992279 : Nat := 2049958033851090923752349

theorem tailTrace_3992279 : CollatzResearch.WordTrace tailWord_3992279 prefixEnd_3992279 2049958033851090923752349 := by
  unfold tailWord_3992279
  simp only [CollatzResearch.WordTrace]
  refine ⟨145610377503662484815291891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97073585002441656543527927 145610377503662484815291891)
  ·
    refine ⟨218415566255493727222937837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145610377503662484815291891 218415566255493727222937837)
    ·
      refine ⟨81905837345810147708601689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218415566255493727222937837 81905837345810147708601689)
      ·
        refine ⟨61429378009357610781451267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81905837345810147708601689 61429378009357610781451267)
        ·
          refine ⟨92144067014036416172176901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61429378009357610781451267 92144067014036416172176901)
          ·
            refine ⟨17277012565131828032283169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92144067014036416172176901 17277012565131828032283169)
            ·
              refine ⟨12957759423848871024212377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17277012565131828032283169 12957759423848871024212377)
              ·
                refine ⟨9718319567886653268159283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12957759423848871024212377 9718319567886653268159283)
                ·
                  refine ⟨14577479351829979902238925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9718319567886653268159283 14577479351829979902238925)
                  ·
                    refine ⟨5466554756936242463339597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14577479351829979902238925 5466554756936242463339597)
                    ·
                      refine ⟨2049958033851090923752349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5466554756936242463339597 2049958033851090923752349)
                      ·
                        rfl

theorem cell23_3992279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_3992279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992279 prefixEnd_3992279 := by exact prefixLift 3992279
  have htrace : WordTrace (prefixWord ++ tailWord_3992279) baseStart_3992279 baseEnd_3992279 := by
    simpa [prefixWord, tailWord_3992279, baseEnd_3992279] using wordTrace_append hprefix tailTrace_3992279
  have hstable : (prefixWord ++ tailWord_3992279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992279).length < 2 ^ (prefixWord ++ tailWord_3992279).sum := by decide
  have hdescent : baseEnd_3992279 < baseStart_3992279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992280 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 1, 2, 2]
def baseStart_3992280 : Nat := 118140960795 + 3992280 * 2 ^ 59
def prefixEnd_3992280 : Nat := 4983230072969 + 3 ^ 40 * 3992280 * 2
def baseEnd_3992280 : Nat := 2049958547331745419839845

theorem tailTrace_3992280 : CollatzResearch.WordTrace tailWord_3992280 prefixEnd_3992280 2049958547331745419839845 := by
  unfold tailWord_3992280
  simp only [CollatzResearch.WordTrace]
  refine ⟨72805206988329430993039147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97073609317772574657385529 72805206988329430993039147)
  ·
    refine ⟨109207810482494146489558721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72805206988329430993039147 109207810482494146489558721)
    ·
      refine ⟨81905857861870609867169041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109207810482494146489558721 81905857861870609867169041)
      ·
        refine ⟨61429393396402957400376781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81905857861870609867169041 61429393396402957400376781)
        ·
          refine ⟨23036022523651109025141293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61429393396402957400376781 23036022523651109025141293)
          ·
            refine ⟨8638508446369165884427985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23036022523651109025141293 8638508446369165884427985)
            ·
              refine ⟨6478881334776874413320989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8638508446369165884427985 6478881334776874413320989)
              ·
                refine ⟨2429580500541327904995371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6478881334776874413320989 2429580500541327904995371)
                ·
                  refine ⟨3644370750811991857493057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429580500541327904995371 3644370750811991857493057)
                  ·
                    refine ⟨2733278063108993893119793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644370750811991857493057 2733278063108993893119793)
                    ·
                      refine ⟨2049958547331745419839845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733278063108993893119793 2049958547331745419839845)
                      ·
                        rfl

theorem cell23_3992280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_3992280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992280 prefixEnd_3992280 := by exact prefixLift 3992280
  have htrace : WordTrace (prefixWord ++ tailWord_3992280) baseStart_3992280 baseEnd_3992280 := by
    simpa [prefixWord, tailWord_3992280, baseEnd_3992280] using wordTrace_append hprefix tailTrace_3992280
  have hstable : (prefixWord ++ tailWord_3992280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992280).length < 2 ^ (prefixWord ++ tailWord_3992280).sum := by decide
  have hdescent : baseEnd_3992280 < baseStart_3992280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992312 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_3992312 : Nat := 118140960795 + 3992312 * 2 ^ 59
def prefixEnd_3992312 : Nat := 4983230072969 + 3 ^ 40 * 3992312 * 2
def baseEnd_3992312 : Nat := 683324992904229764879899

theorem tailTrace_3992312 : CollatzResearch.WordTrace tailWord_3992312 prefixEnd_3992312 683324992904229764879899 := by
  unfold tailWord_3992312
  simp only [CollatzResearch.WordTrace]
  refine ⟨72805790556271465725621595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97074387408361954300828793 72805790556271465725621595)
  ·
    refine ⟨109208685834407198588432393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72805790556271465725621595 109208685834407198588432393)
    ·
      refine ⟨81906514375805398941324295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109208685834407198588432393 81906514375805398941324295)
      ·
        refine ⟨122859771563708098411986443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81906514375805398941324295 122859771563708098411986443)
        ·
          refine ⟨184289657345562147617979665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122859771563708098411986443 184289657345562147617979665)
          ·
            refine ⟨138217243009171610713484749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184289657345562147617979665 138217243009171610713484749)
            ·
              refine ⟨51831466128439354017556781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138217243009171610713484749 51831466128439354017556781)
              ·
                refine ⟨19436799798164757756583793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51831466128439354017556781 19436799798164757756583793)
                ·
                  refine ⟨14577599848623568317437845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19436799798164757756583793 14577599848623568317437845)
                  ·
                    refine ⟨683324992904229764879899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14577599848623568317437845 683324992904229764879899)
                    ·
                      rfl

theorem cell23_3992312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_3992312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992312 prefixEnd_3992312 := by exact prefixLift 3992312
  have htrace : WordTrace (prefixWord ++ tailWord_3992312) baseStart_3992312 baseEnd_3992312 := by
    simpa [prefixWord, tailWord_3992312, baseEnd_3992312] using wordTrace_append hprefix tailTrace_3992312
  have hstable : (prefixWord ++ tailWord_3992312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992312).length < 2 ^ (prefixWord ++ tailWord_3992312).sum := by decide
  have hdescent : baseEnd_3992312 < baseStart_3992312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992353 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3992353 : Nat := 118140960795 + 3992353 * 2 ^ 59
def prefixEnd_3992353 : Nat := 4983230072969 + 3 ^ 40 * 3992353 * 2
def baseEnd_3992353 : Nat := 2049996031419523634227009

theorem tailTrace_3992353 : CollatzResearch.WordTrace tailWord_3992353 prefixEnd_3992353 2049996031419523634227009 := by
  unfold tailWord_3992353
  simp only [CollatzResearch.WordTrace]
  refine ⟨145613076505394395453485713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97075384336929596968990475 145613076505394395453485713)
  ·
    refine ⟨109209807379045796590114285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145613076505394395453485713 109209807379045796590114285)
    ·
      refine ⟨40953677767142173721292857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109209807379045796590114285 40953677767142173721292857)
      ·
        refine ⟨30715258325356630290969643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40953677767142173721292857 30715258325356630290969643)
        ·
          refine ⟨46072887488034945436454465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30715258325356630290969643 46072887488034945436454465)
          ·
            refine ⟨34554665616026209077340849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46072887488034945436454465 34554665616026209077340849)
            ·
              refine ⟨25915999212019656808005637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34554665616026209077340849 25915999212019656808005637)
              ·
                refine ⟨4859249852253685651501057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25915999212019656808005637 4859249852253685651501057)
                ·
                  refine ⟨3644437389190264238625793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859249852253685651501057 3644437389190264238625793)
                  ·
                    refine ⟨2733328041892698178969345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644437389190264238625793 2733328041892698178969345)
                    ·
                      refine ⟨2049996031419523634227009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733328041892698178969345 2049996031419523634227009)
                      ·
                        rfl

theorem cell23_3992353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3992353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992353 prefixEnd_3992353 := by exact prefixLift 3992353
  have htrace : WordTrace (prefixWord ++ tailWord_3992353) baseStart_3992353 baseEnd_3992353 := by
    simpa [prefixWord, tailWord_3992353, baseEnd_3992353] using wordTrace_append hprefix tailTrace_3992353
  have hstable : (prefixWord ++ tailWord_3992353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992353).length < 2 ^ (prefixWord ++ tailWord_3992353).sum := by decide
  have hdescent : baseEnd_3992353 < baseStart_3992353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992369 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_3992369 : Nat := 118140960795 + 3992369 * 2 ^ 59
def prefixEnd_3992369 : Nat := 4983230072969 + 3 ^ 40 * 3992369 * 2
def baseEnd_3992369 : Nat := 2050004247109995571626935

theorem tailTrace_3992369 : CollatzResearch.WordTrace tailWord_3992369 prefixEnd_3992369 2050004247109995571626935 := by
  unfold tailWord_3992369
  simp only [CollatzResearch.WordTrace]
  refine ⟨145613660073336430186068161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97075773382224286790712107 145613660073336430186068161)
  ·
    refine ⟨109210245055002322639551121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145613660073336430186068161 109210245055002322639551121)
    ·
      refine ⟨81907683791251741979663341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109210245055002322639551121 81907683791251741979663341)
      ·
        refine ⟨30715381421719403242373753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81907683791251741979663341 30715381421719403242373753)
        ·
          refine ⟨23036536066289552431780315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30715381421719403242373753 23036536066289552431780315)
          ·
            refine ⟨34554804099434328647670473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23036536066289552431780315 34554804099434328647670473)
            ·
              refine ⟨25916103074575746485752855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34554804099434328647670473 25916103074575746485752855)
              ·
                refine ⟨38874154611863619728629283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25916103074575746485752855 38874154611863619728629283)
                ·
                  refine ⟨58311231917795429592943925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38874154611863619728629283 58311231917795429592943925)
                  ·
                    refine ⟨5466677992293321524338493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58311231917795429592943925 5466677992293321524338493)
                    ·
                      refine ⟨2050004247109995571626935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5466677992293321524338493 2050004247109995571626935)
                      ·
                        rfl

theorem cell23_3992369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_3992369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992369 prefixEnd_3992369 := by exact prefixLift 3992369
  have htrace : WordTrace (prefixWord ++ tailWord_3992369) baseStart_3992369 baseEnd_3992369 := by
    simpa [prefixWord, tailWord_3992369, baseEnd_3992369] using wordTrace_append hprefix tailTrace_3992369
  have hstable : (prefixWord ++ tailWord_3992369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992369).length < 2 ^ (prefixWord ++ tailWord_3992369).sum := by decide
  have hdescent : baseEnd_3992369 < baseStart_3992369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992374 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3992374 : Nat := 118140960795 + 3992374 * 2 ^ 59
def prefixEnd_3992374 : Nat := 4983230072969 + 3 ^ 40 * 3992374 * 2
def baseEnd_3992374 : Nat := 2050006814513268052064413

theorem tailTrace_3992374 : CollatzResearch.WordTrace tailWord_3992374 prefixEnd_3992374 2050006814513268052064413 := by
  unfold tailWord_3992374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100865152394894752500011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97075894958878877360000117 9100865152394894752500011)
  ·
    refine ⟨13651297728592342128750017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9100865152394894752500011 13651297728592342128750017)
    ·
      refine ⟨10238473296444256596562513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13651297728592342128750017 10238473296444256596562513)
      ·
        refine ⟨7678854972333192447421885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10238473296444256596562513 7678854972333192447421885)
        ·
          refine ⟨2879570614624947167783207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7678854972333192447421885 2879570614624947167783207)
          ·
            refine ⟨4319355921937420751674811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879570614624947167783207 4319355921937420751674811)
            ·
              refine ⟨6479033882906131127512217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319355921937420751674811 6479033882906131127512217)
              ·
                refine ⟨4859275412179598345634163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6479033882906131127512217 4859275412179598345634163)
                ·
                  refine ⟨7288913118269397518451245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859275412179598345634163 7288913118269397518451245)
                  ·
                    refine ⟨2733342419351024069419217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7288913118269397518451245 2733342419351024069419217)
                    ·
                      refine ⟨2050006814513268052064413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733342419351024069419217 2050006814513268052064413)
                      ·
                        rfl

theorem cell23_3992374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3992374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992374 prefixEnd_3992374 := by exact prefixLift 3992374
  have htrace : WordTrace (prefixWord ++ tailWord_3992374) baseStart_3992374 baseEnd_3992374 := by
    simpa [prefixWord, tailWord_3992374, baseEnd_3992374] using wordTrace_append hprefix tailTrace_3992374
  have hstable : (prefixWord ++ tailWord_3992374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992374).length < 2 ^ (prefixWord ++ tailWord_3992374).sum := by decide
  have hdescent : baseEnd_3992374 < baseStart_3992374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992453 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_3992453 : Nat := 118140960795 + 3992453 * 2 ^ 59
def prefixEnd_3992453 : Nat := 4983230072969 + 3 ^ 40 * 3992453 * 2
def baseEnd_3992453 : Nat := 683349126494991080992183

theorem tailTrace_3992453 : CollatzResearch.WordTrace tailWord_3992453 prefixEnd_3992453 683349126494991080992183 := by
  unfold tailWord_3992453
  simp only [CollatzResearch.WordTrace]
  refine ⟨145616723805032112532126013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97077815870021408354750675 145616723805032112532126013)
  ·
    refine ⟨54606271426887042199547255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145616723805032112532126013 54606271426887042199547255)
    ·
      refine ⟨81909407140330563299320883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54606271426887042199547255 81909407140330563299320883)
      ·
        refine ⟨122864110710495844948981325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81909407140330563299320883 122864110710495844948981325)
        ·
          refine ⟨46074041516435941855867997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122864110710495844948981325 46074041516435941855867997)
          ·
            refine ⟨17277765568663478195950499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46074041516435941855867997 17277765568663478195950499)
            ·
              refine ⟨25916648352995217293925749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17277765568663478195950499 25916648352995217293925749)
              ·
                refine ⟨2429685783093301621305539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25916648352995217293925749 2429685783093301621305539)
                ·
                  refine ⟨3644528674639952431958309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429685783093301621305539 3644528674639952431958309)
                  ·
                    refine ⟨683349126494991080992183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3644528674639952431958309 683349126494991080992183)
                    ·
                      rfl

theorem cell23_3992453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_3992453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992453 prefixEnd_3992453 := by exact prefixLift 3992453
  have htrace : WordTrace (prefixWord ++ tailWord_3992453) baseStart_3992453 baseEnd_3992453 := by
    simpa [prefixWord, tailWord_3992453, baseEnd_3992453] using wordTrace_append hprefix tailTrace_3992453
  have hstable : (prefixWord ++ tailWord_3992453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992453).length < 2 ^ (prefixWord ++ tailWord_3992453).sum := by decide
  have hdescent : baseEnd_3992453 < baseStart_3992453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992469 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3992469 : Nat := 118140960795 + 3992469 * 2 ^ 59
def prefixEnd_3992469 : Nat := 4983230072969 + 3 ^ 40 * 3992469 * 2
def baseEnd_3992469 : Nat := 2050055595175445180376475

theorem tailTrace_3992469 : CollatzResearch.WordTrace tailWord_3992469 prefixEnd_3992469 2050055595175445180376475 := by
  unfold tailWord_3992469
  simp only [CollatzResearch.WordTrace]
  refine ⟨145617307372974147264708461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97078204915316098176472307 145617307372974147264708461)
  ·
    refine ⟨54606490264865305224265673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145617307372974147264708461 54606490264865305224265673)
    ·
      refine ⟨40954867698648978918199255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54606490264865305224265673 40954867698648978918199255)
      ·
        refine ⟨61432301547973468377298883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40954867698648978918199255 61432301547973468377298883)
        ·
          refine ⟨92148452321960202565948325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61432301547973468377298883 92148452321960202565948325)
          ·
            refine ⟨17277834810367537981115311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92148452321960202565948325 17277834810367537981115311)
            ·
              refine ⟨25916752215551306971672967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17277834810367537981115311 25916752215551306971672967)
              ·
                refine ⟨38875128323326960457509451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25916752215551306971672967 38875128323326960457509451)
                ·
                  refine ⟨58312692484990440686264177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38875128323326960457509451 58312692484990440686264177)
                  ·
                    refine ⟨43734519363742830514698133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58312692484990440686264177 43734519363742830514698133)
                    ·
                      refine ⟨2050055595175445180376475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43734519363742830514698133 2050055595175445180376475)
                      ·
                        rfl

theorem cell23_3992469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3992469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992469 prefixEnd_3992469 := by exact prefixLift 3992469
  have htrace : WordTrace (prefixWord ++ tailWord_3992469) baseStart_3992469 baseEnd_3992469 := by
    simpa [prefixWord, tailWord_3992469, baseEnd_3992469] using wordTrace_append hprefix tailTrace_3992469
  have hstable : (prefixWord ++ tailWord_3992469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992469).length < 2 ^ (prefixWord ++ tailWord_3992469).sum := by decide
  have hdescent : baseEnd_3992469 < baseStart_3992469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992520 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_3992520 : Nat := 118140960795 + 3992520 * 2 ^ 59
def prefixEnd_3992520 : Nat := 4983230072969 + 3 ^ 40 * 3992520 * 2
def baseEnd_3992520 : Nat := 2050081782688824480838741

theorem tailTrace_3992520 : CollatzResearch.WordTrace tailWord_3992520 prefixEnd_3992520 2050081782688824480838741 := by
  unfold tailWord_3992520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72809583747894691487407507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97079444997192921983210009 72809583747894691487407507)
  ·
    refine ⟨109214375621842037231111261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72809583747894691487407507 109214375621842037231111261)
    ·
      refine ⟨40955390858190763961666723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109214375621842037231111261 40955390858190763961666723)
      ·
        refine ⟨61433086287286145942500085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40955390858190763961666723 61433086287286145942500085)
        ·
          refine ⟨5759351839433076182109383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61433086287286145942500085 5759351839433076182109383)
          ·
            refine ⟨8639027759149614273164075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759351839433076182109383 8639027759149614273164075)
            ·
              refine ⟨12958541638724421409746113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639027759149614273164075 12958541638724421409746113)
              ·
                refine ⟨9718906229043316057309585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12958541638724421409746113 9718906229043316057309585)
                ·
                  refine ⟨7289179671782487042982189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9718906229043316057309585 7289179671782487042982189)
                  ·
                    refine ⟨2733442376918432641118321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7289179671782487042982189 2733442376918432641118321)
                    ·
                      refine ⟨2050081782688824480838741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733442376918432641118321 2050081782688824480838741)
                      ·
                        rfl

theorem cell23_3992520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_3992520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992520 prefixEnd_3992520 := by exact prefixLift 3992520
  have htrace : WordTrace (prefixWord ++ tailWord_3992520) baseStart_3992520 baseEnd_3992520 := by
    simpa [prefixWord, tailWord_3992520, baseEnd_3992520] using wordTrace_append hprefix tailTrace_3992520
  have hstable : (prefixWord ++ tailWord_3992520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992520).length < 2 ^ (prefixWord ++ tailWord_3992520).sum := by decide
  have hdescent : baseEnd_3992520 < baseStart_3992520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992527 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 1, 1, 3]
def baseStart_3992527 : Nat := 118140960795 + 3992527 * 2 ^ 59
def prefixEnd_3992527 : Nat := 4983230072969 + 3 ^ 40 * 3992527 * 2
def baseEnd_3992527 : Nat := 2050085377053405953451209

theorem tailTrace_3992527 : CollatzResearch.WordTrace tailWord_3992527 prefixEnd_3992527 2050085377053405953451209 := by
  unfold tailWord_3992527
  simp only [CollatzResearch.WordTrace]
  refine ⟨145619422806764023170319835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97079615204509348780213223 145619422806764023170319835)
  ·
    refine ⟨218429134210146034755479753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145619422806764023170319835 218429134210146034755479753)
    ·
      refine ⟨163821850657609526066609815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218429134210146034755479753 163821850657609526066609815)
      ·
        refine ⟨245732775986414289099914723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163821850657609526066609815 245732775986414289099914723)
        ·
          refine ⟨368599163979621433649872085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245732775986414289099914723 368599163979621433649872085)
          ·
            refine ⟨8639042905772377351168877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 368599163979621433649872085 8639042905772377351168877)
            ·
              refine ⟨3239641089664641506688329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8639042905772377351168877 3239641089664641506688329)
              ·
                refine ⟨2429730817248481130016247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239641089664641506688329 2429730817248481130016247)
                ·
                  refine ⟨3644596225872721695024371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429730817248481130016247 3644596225872721695024371)
                  ·
                    refine ⟨5466894338809082542536557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3644596225872721695024371 5466894338809082542536557)
                    ·
                      refine ⟨2050085377053405953451209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5466894338809082542536557 2050085377053405953451209)
                      ·
                        rfl

theorem cell23_3992527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 1, 3].length) (baseStart_3992527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992527 prefixEnd_3992527 := by exact prefixLift 3992527
  have htrace : WordTrace (prefixWord ++ tailWord_3992527) baseStart_3992527 baseEnd_3992527 := by
    simpa [prefixWord, tailWord_3992527, baseEnd_3992527] using wordTrace_append hprefix tailTrace_3992527
  have hstable : (prefixWord ++ tailWord_3992527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992527).length < 2 ^ (prefixWord ++ tailWord_3992527).sum := by decide
  have hdescent : baseEnd_3992527 < baseStart_3992527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992529 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_3992529 : Nat := 118140960795 + 3992529 * 2 ^ 59
def prefixEnd_3992529 : Nat := 4983230072969 + 3 ^ 40 * 3992529 * 2
def baseEnd_3992529 : Nat := 2050086404014714945626199

theorem tailTrace_3992529 : CollatzResearch.WordTrace tailWord_3992529 prefixEnd_3992529 2050086404014714945626199 := by
  unfold tailWord_3992529
  simp only [CollatzResearch.WordTrace]
  refine ⟨145619495752756777511892641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97079663835171185007928427 145619495752756777511892641)
  ·
    refine ⟨109214621814567583133919481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145619495752756777511892641 109214621814567583133919481)
    ·
      refine ⟨81910966360925687350439611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109214621814567583133919481 81910966360925687350439611)
      ·
        refine ⟨122866449541388531025659417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81910966360925687350439611 122866449541388531025659417)
        ·
          refine ⟨92149837156041398269244563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122866449541388531025659417 92149837156041398269244563)
          ·
            refine ⟨138224755734062097403866845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92149837156041398269244563 138224755734062097403866845)
            ·
              refine ⟨51834283400273286526450067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138224755734062097403866845 51834283400273286526450067)
              ·
                refine ⟨77751425100409929789675101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51834283400273286526450067 77751425100409929789675101)
                ·
                  refine ⟨29156784412653723671128163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77751425100409929789675101 29156784412653723671128163)
                  ·
                    refine ⟨43735176618980585506692245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29156784412653723671128163 43735176618980585506692245)
                    ·
                      refine ⟨2050086404014714945626199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43735176618980585506692245 2050086404014714945626199)
                      ·
                        rfl

theorem cell23_3992529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_3992529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992529 prefixEnd_3992529 := by exact prefixLift 3992529
  have htrace : WordTrace (prefixWord ++ tailWord_3992529) baseStart_3992529 baseEnd_3992529 := by
    simpa [prefixWord, tailWord_3992529, baseEnd_3992529] using wordTrace_append hprefix tailTrace_3992529
  have hstable : (prefixWord ++ tailWord_3992529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992529).length < 2 ^ (prefixWord ++ tailWord_3992529).sum := by decide
  have hdescent : baseEnd_3992529 < baseStart_3992529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992536 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3992536 : Nat := 118140960795 + 3992536 * 2 ^ 59
def prefixEnd_3992536 : Nat := 4983230072969 + 3 ^ 40 * 3992536 * 2
def baseEnd_3992536 : Nat := 2050089998379296418238667

theorem tailTrace_3992536 : CollatzResearch.WordTrace tailWord_3992536 prefixEnd_3992536 2050089998379296418238667 := by
  unfold tailWord_3992536
  simp only [CollatzResearch.WordTrace]
  refine ⟨72809875531865708853698731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97079834042487611804931641 72809875531865708853698731)
  ·
    refine ⟨109214813297798563280548097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72809875531865708853698731 109214813297798563280548097)
    ·
      refine ⟨81911109973348922460411073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109214813297798563280548097 81911109973348922460411073)
      ·
        refine ⟨61433332480011691845308305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81911109973348922460411073 61433332480011691845308305)
        ·
          refine ⟨46074999360008768883981229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61433332480011691845308305 46074999360008768883981229)
          ·
            refine ⟨17278124760003288331492961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46074999360008768883981229 17278124760003288331492961)
            ·
              refine ⟨12958593570002466248619721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17278124760003288331492961 12958593570002466248619721)
              ·
                refine ⟨9718945177501849686464791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12958593570002466248619721 9718945177501849686464791)
                ·
                  refine ⟨14578417766252774529697187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9718945177501849686464791 14578417766252774529697187)
                  ·
                    refine ⟨21867626649379161794545781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14578417766252774529697187 21867626649379161794545781)
                    ·
                      refine ⟨2050089998379296418238667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21867626649379161794545781 2050089998379296418238667)
                      ·
                        rfl

theorem cell23_3992536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3992536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992536 prefixEnd_3992536 := by exact prefixLift 3992536
  have htrace : WordTrace (prefixWord ++ tailWord_3992536) baseStart_3992536 baseEnd_3992536 := by
    simpa [prefixWord, tailWord_3992536, baseEnd_3992536] using wordTrace_append hprefix tailTrace_3992536
  have hstable : (prefixWord ++ tailWord_3992536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992536).length < 2 ^ (prefixWord ++ tailWord_3992536).sum := by decide
  have hdescent : baseEnd_3992536 < baseStart_3992536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992578 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_3992578 : Nat := 118140960795 + 3992578 * 2 ^ 59
def prefixEnd_3992578 : Nat := 4983230072969 + 3 ^ 40 * 3992578 * 2
def baseEnd_3992578 : Nat := 2050111564566785253913475

theorem tailTrace_3992578 : CollatzResearch.WordTrace tailWord_3992578 prefixEnd_3992578 2050111564566785253913475 := by
  unfold tailWord_3992578
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405320732394814720106597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97080855286386172586950925 36405320732394814720106597)
  ·
    refine ⟨6825997637324027760019987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36405320732394814720106597 6825997637324027760019987)
    ·
      refine ⟨10238996455986041640029981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825997637324027760019987 10238996455986041640029981)
      ·
        refine ⟨3839623670994765615011243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10238996455986041640029981 3839623670994765615011243)
        ·
          refine ⟨5759435506492148422516865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839623670994765615011243 5759435506492148422516865)
          ·
            refine ⟨4319576629869111316887649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5759435506492148422516865 4319576629869111316887649)
            ·
              refine ⟨3239682472401833487665737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4319576629869111316887649 3239682472401833487665737)
              ·
                refine ⟨2429761854301375115749303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239682472401833487665737 2429761854301375115749303)
                ·
                  refine ⟨3644642781452062673623955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429761854301375115749303 3644642781452062673623955)
                  ·
                    refine ⟨5466964172178094010435933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3644642781452062673623955 5466964172178094010435933)
                    ·
                      refine ⟨2050111564566785253913475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5466964172178094010435933 2050111564566785253913475)
                      ·
                        rfl

theorem cell23_3992578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_3992578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992578 prefixEnd_3992578 := by exact prefixLift 3992578
  have htrace : WordTrace (prefixWord ++ tailWord_3992578) baseStart_3992578 baseEnd_3992578 := by
    simpa [prefixWord, tailWord_3992578, baseEnd_3992578] using wordTrace_append hprefix tailTrace_3992578
  have hstable : (prefixWord ++ tailWord_3992578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992578).length < 2 ^ (prefixWord ++ tailWord_3992578).sum := by decide
  have hdescent : baseEnd_3992578 < baseStart_3992578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992579 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_3992579 : Nat := 118140960795 + 3992579 * 2 ^ 59
def prefixEnd_3992579 : Nat := 4983230072969 + 3 ^ 40 * 3992579 * 2
def baseEnd_3992579 : Nat := 2050112078047439750000969

theorem tailTrace_3992579 : CollatzResearch.WordTrace tailWord_3992579 prefixEnd_3992579 2050112078047439750000969 := by
  unfold tailWord_3992579
  simp only [CollatzResearch.WordTrace]
  refine ⟨145621319402575636051212791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97080879601717090700808527 145621319402575636051212791)
  ·
    refine ⟨218431979103863454076819187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145621319402575636051212791 218431979103863454076819187)
    ·
      refine ⟨327647968655795181115228781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218431979103863454076819187 327647968655795181115228781)
      ·
        refine ⟨122867988245923192918210793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327647968655795181115228781 122867988245923192918210793)
        ·
          refine ⟨92150991184442394688658095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122867988245923192918210793 92150991184442394688658095)
          ·
            refine ⟨138226486776663592032987143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92150991184442394688658095 138226486776663592032987143)
            ·
              refine ⟨207339730164995388049480715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138226486776663592032987143 207339730164995388049480715)
              ·
                refine ⟨311009595247493082074221073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207339730164995388049480715 311009595247493082074221073)
                ·
                  refine ⟨233257196435619811555665805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311009595247493082074221073 233257196435619811555665805)
                  ·
                    refine ⟨87471448663357429333374677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233257196435619811555665805 87471448663357429333374677)
                    ·
                      refine ⟨2050112078047439750000969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87471448663357429333374677 2050112078047439750000969)
                      ·
                        rfl

theorem cell23_3992579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_3992579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992579 prefixEnd_3992579 := by exact prefixLift 3992579
  have htrace : WordTrace (prefixWord ++ tailWord_3992579) baseStart_3992579 baseEnd_3992579 := by
    simpa [prefixWord, tailWord_3992579, baseEnd_3992579] using wordTrace_append hprefix tailTrace_3992579
  have hstable : (prefixWord ++ tailWord_3992579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992579).length < 2 ^ (prefixWord ++ tailWord_3992579).sum := by decide
  have hdescent : baseEnd_3992579 < baseStart_3992579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992584 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_3992584 : Nat := 118140960795 + 3992584 * 2 ^ 59
def prefixEnd_3992584 : Nat := 4983230072969 + 3 ^ 40 * 3992584 * 2
def baseEnd_3992584 : Nat := 2050114645450712230438447

theorem tailTrace_3992584 : CollatzResearch.WordTrace tailWord_3992584 prefixEnd_3992584 2050114645450712230438447 := by
  unfold tailWord_3992584
  simp only [CollatzResearch.WordTrace]
  refine ⟨72810750883778760952572403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97081001178371681270096537 72810750883778760952572403)
  ·
    refine ⟨109216126325668141428858605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72810750883778760952572403 109216126325668141428858605)
    ·
      refine ⟨40956047372125553035821977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109216126325668141428858605 40956047372125553035821977)
      ·
        refine ⟨30717035529094164776866483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40956047372125553035821977 30717035529094164776866483)
        ·
          refine ⟨46075553293641247165299725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30717035529094164776866483 46075553293641247165299725)
          ·
            refine ⟨17278332485115467686987397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46075553293641247165299725 17278332485115467686987397)
            ·
              refine ⟨3239687340959150191310137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17278332485115467686987397 3239687340959150191310137)
              ·
                refine ⟨2429765505719362643482603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239687340959150191310137 2429765505719362643482603)
                ·
                  refine ⟨3644648258579043965223905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429765505719362643482603 3644648258579043965223905)
                  ·
                    refine ⟨2733486193934282973917929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644648258579043965223905 2733486193934282973917929)
                    ·
                      refine ⟨2050114645450712230438447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733486193934282973917929 2050114645450712230438447)
                      ·
                        rfl

theorem cell23_3992584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_3992584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992584 prefixEnd_3992584 := by exact prefixLift 3992584
  have htrace : WordTrace (prefixWord ++ tailWord_3992584) baseStart_3992584 baseEnd_3992584 := by
    simpa [prefixWord, tailWord_3992584, baseEnd_3992584] using wordTrace_append hprefix tailTrace_3992584
  have hstable : (prefixWord ++ tailWord_3992584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992584).length < 2 ^ (prefixWord ++ tailWord_3992584).sum := by decide
  have hdescent : baseEnd_3992584 < baseStart_3992584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992586 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_3992586 : Nat := 118140960795 + 3992586 * 2 ^ 59
def prefixEnd_3992586 : Nat := 4983230072969 + 3 ^ 40 * 3992586 * 2
def baseEnd_3992586 : Nat := 683371890804007074204479

theorem tailTrace_3992586 : CollatzResearch.WordTrace tailWord_3992586 prefixEnd_3992586 683371890804007074204479 := by
  unfold tailWord_3992586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405393678387569061679403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97081049809033517497811741 36405393678387569061679403)
  ·
    refine ⟨54608090517581353592519105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36405393678387569061679403 54608090517581353592519105)
    ·
      refine ⟨40956067888186015194389329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54608090517581353592519105 40956067888186015194389329)
      ·
        refine ⟨30717050916139511395791997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40956067888186015194389329 30717050916139511395791997)
        ·
          refine ⟨11518894093552316773421999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30717050916139511395791997 11518894093552316773421999)
          ·
            refine ⟨17278341140328475160132999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11518894093552316773421999 17278341140328475160132999)
            ·
              refine ⟨25917511710492712740199499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17278341140328475160132999 25917511710492712740199499)
              ·
                refine ⟨38876267565739069110299249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25917511710492712740199499 38876267565739069110299249)
                ·
                  refine ⟨29157200674304301832724437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38876267565739069110299249 29157200674304301832724437)
                  ·
                    refine ⟨683371890804007074204479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29157200674304301832724437 683371890804007074204479)
                    ·
                      rfl

theorem cell23_3992586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_3992586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992586 prefixEnd_3992586 := by exact prefixLift 3992586
  have htrace : WordTrace (prefixWord ++ tailWord_3992586) baseStart_3992586 baseEnd_3992586 := by
    simpa [prefixWord, tailWord_3992586, baseEnd_3992586] using wordTrace_append hprefix tailTrace_3992586
  have hstable : (prefixWord ++ tailWord_3992586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992586).length < 2 ^ (prefixWord ++ tailWord_3992586).sum := by decide
  have hdescent : baseEnd_3992586 < baseStart_3992586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992600 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3992600 : Nat := 118140960795 + 3992600 * 2 ^ 59
def prefixEnd_3992600 : Nat := 4983230072969 + 3 ^ 40 * 3992600 * 2
def baseEnd_3992600 : Nat := 2050122861141184167838373

theorem tailTrace_3992600 : CollatzResearch.WordTrace tailWord_3992600 prefixEnd_3992600 2050122861141184167838373 := by
  unfold tailWord_3992600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72811042667749778318863627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97081390223666371091818169 72811042667749778318863627)
  ·
    refine ⟨109216564001624667478295441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72811042667749778318863627 109216564001624667478295441)
    ·
      refine ⟨81912423001218500608721581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109216564001624667478295441 81912423001218500608721581)
      ·
        refine ⟨30717158625456937728270593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81912423001218500608721581 30717158625456937728270593)
        ·
          refine ⟨23037868969092703296202945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30717158625456937728270593 23037868969092703296202945)
          ·
            refine ⟨17278401726819527472152209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23037868969092703296202945 17278401726819527472152209)
            ·
              refine ⟨12958801295114645604114157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17278401726819527472152209 12958801295114645604114157)
              ·
                refine ⟨4859550485667992101542809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12958801295114645604114157 4859550485667992101542809)
                ·
                  refine ⟨3644662864250994076157107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859550485667992101542809 3644662864250994076157107)
                  ·
                    refine ⟨5466994296376491114235661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3644662864250994076157107 5466994296376491114235661)
                    ·
                      refine ⟨2050122861141184167838373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5466994296376491114235661 2050122861141184167838373)
                      ·
                        rfl

theorem cell23_3992600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3992600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992600 prefixEnd_3992600 := by exact prefixLift 3992600
  have htrace : WordTrace (prefixWord ++ tailWord_3992600) baseStart_3992600 baseEnd_3992600 := by
    simpa [prefixWord, tailWord_3992600, baseEnd_3992600] using wordTrace_append hprefix tailTrace_3992600
  have hstable : (prefixWord ++ tailWord_3992600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992600).length < 2 ^ (prefixWord ++ tailWord_3992600).sum := by decide
  have hdescent : baseEnd_3992600 < baseStart_3992600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992610 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_3992610 : Nat := 118140960795 + 3992610 * 2 ^ 59
def prefixEnd_3992610 : Nat := 4983230072969 + 3 ^ 40 * 3992610 * 2
def baseEnd_3992610 : Nat := 2050127995947729128713327

theorem tailTrace_3992610 : CollatzResearch.WordTrace tailWord_3992610 prefixEnd_3992610 2050127995947729128713327 := by
  unfold tailWord_3992610
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405612516365832086397821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97081633376975552230394189 36405612516365832086397821)
  ·
    refine ⟨13652104693637187032399183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36405612516365832086397821 13652104693637187032399183)
    ·
      refine ⟨20478157040455780548598775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13652104693637187032399183 20478157040455780548598775)
      ·
        refine ⟨30717235560683670822898163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20478157040455780548598775 30717235560683670822898163)
        ·
          refine ⟨46075853341025506234347245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30717235560683670822898163 46075853341025506234347245)
          ·
            refine ⟨17278445002884564837880217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46075853341025506234347245 17278445002884564837880217)
            ·
              refine ⟨12958833752163423628410163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17278445002884564837880217 12958833752163423628410163)
              ·
                refine ⟨19438250628245135442615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958833752163423628410163 19438250628245135442615245)
                ·
                  refine ⟨7289343985591925790980717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19438250628245135442615245 7289343985591925790980717)
                  ·
                    refine ⟨2733503994596972171617769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7289343985591925790980717 2733503994596972171617769)
                    ·
                      refine ⟨2050127995947729128713327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733503994596972171617769 2050127995947729128713327)
                      ·
                        rfl

theorem cell23_3992610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_3992610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992610 prefixEnd_3992610 := by exact prefixLift 3992610
  have htrace : WordTrace (prefixWord ++ tailWord_3992610) baseStart_3992610 baseEnd_3992610 := by
    simpa [prefixWord, tailWord_3992610, baseEnd_3992610] using wordTrace_append hprefix tailTrace_3992610
  have hstable : (prefixWord ++ tailWord_3992610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992610).length < 2 ^ (prefixWord ++ tailWord_3992610).sum := by decide
  have hdescent : baseEnd_3992610 < baseStart_3992610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992626 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3992626 : Nat := 118140960795 + 3992626 * 2 ^ 59
def prefixEnd_3992626 : Nat := 4983230072969 + 3 ^ 40 * 3992626 * 2
def baseEnd_3992626 : Nat := 2050136211638201066113253

theorem tailTrace_3992626 : CollatzResearch.WordTrace tailWord_3992626 prefixEnd_3992626 2050136211638201066113253 := by
  unfold tailWord_3992626
  simp only [CollatzResearch.WordTrace]
  refine ⟨36405758408351340769543433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97082022422270242052115821 36405758408351340769543433)
  ·
    refine ⟨27304318806263505577157575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36405758408351340769543433 27304318806263505577157575)
    ·
      refine ⟨40956478209395258365736363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27304318806263505577157575 40956478209395258365736363)
      ·
        refine ⟨61434717314092887548604545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40956478209395258365736363 61434717314092887548604545)
        ·
          refine ⟨46076037985569665661453409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61434717314092887548604545 46076037985569665661453409)
          ·
            refine ⟨34557028489177249246090057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46076037985569665661453409 34557028489177249246090057)
            ·
              refine ⟨25917771366882936934567543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34557028489177249246090057 25917771366882936934567543)
              ·
                refine ⟨38876657050324405401851315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25917771366882936934567543 38876657050324405401851315)
                ·
                  refine ⟨58314985575486608102776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38876657050324405401851315 58314985575486608102776973)
                  ·
                    refine ⟨21868119590807478038541365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58314985575486608102776973 21868119590807478038541365)
                    ·
                      refine ⟨2050136211638201066113253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21868119590807478038541365 2050136211638201066113253)
                      ·
                        rfl

theorem cell23_3992626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3992626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992626 prefixEnd_3992626 := by exact prefixLift 3992626
  have htrace : WordTrace (prefixWord ++ tailWord_3992626) baseStart_3992626 baseEnd_3992626 := by
    simpa [prefixWord, tailWord_3992626, baseEnd_3992626] using wordTrace_append hprefix tailTrace_3992626
  have hstable : (prefixWord ++ tailWord_3992626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992626).length < 2 ^ (prefixWord ++ tailWord_3992626).sum := by decide
  have hdescent : baseEnd_3992626 < baseStart_3992626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992640 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2]
def baseStart_3992640 : Nat := 118140960795 + 3992640 * 2 ^ 59
def prefixEnd_3992640 : Nat := 4983230072969 + 3 ^ 40 * 3992640 * 2
def baseEnd_3992640 : Nat := 2050143400367364011338189

theorem tailTrace_3992640 : CollatzResearch.WordTrace tailWord_3992640 prefixEnd_3992640 2050143400367364011338189 := by
  unfold tailWord_3992640
  simp only [CollatzResearch.WordTrace]
  refine ⟨72811772127677321734591687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97082362836903095646122249 72811772127677321734591687)
  ·
    refine ⟨109217658191515982601887531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72811772127677321734591687 109217658191515982601887531)
    ·
      refine ⟨163826487287273973902831297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109217658191515982601887531 163826487287273973902831297)
      ·
        refine ⟨122869865465455480427123473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163826487287273973902831297 122869865465455480427123473)
        ·
          refine ⟨92152399099091610320342605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122869865465455480427123473 92152399099091610320342605)
          ·
            refine ⟨34557149662159353870128477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92152399099091610320342605 34557149662159353870128477)
            ·
              refine ⟨12958931123309757701298179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34557149662159353870128477 12958931123309757701298179)
              ·
                refine ⟨19438396684964636551947269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12958931123309757701298179 19438396684964636551947269)
                ·
                  refine ⟨3644699378430869353490113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19438396684964636551947269 3644699378430869353490113)
                  ·
                    refine ⟨2733524533823152015117585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644699378430869353490113 2733524533823152015117585)
                    ·
                      refine ⟨2050143400367364011338189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733524533823152015117585 2050143400367364011338189)
                      ·
                        rfl

theorem cell23_3992640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_3992640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992640 prefixEnd_3992640 := by exact prefixLift 3992640
  have htrace : WordTrace (prefixWord ++ tailWord_3992640) baseStart_3992640 baseEnd_3992640 := by
    simpa [prefixWord, tailWord_3992640, baseEnd_3992640] using wordTrace_append hprefix tailTrace_3992640
  have hstable : (prefixWord ++ tailWord_3992640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992640).length < 2 ^ (prefixWord ++ tailWord_3992640).sum := by decide
  have hdescent : baseEnd_3992640 < baseStart_3992640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992697 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 5]
def baseStart_3992697 : Nat := 118140960795 + 3992697 * 2 ^ 59
def prefixEnd_3992697 : Nat := 4983230072969 + 3 ^ 40 * 3992697 * 2
def baseEnd_3992697 : Nat := 227796963196074476480603

theorem tailTrace_3992697 : CollatzResearch.WordTrace tailWord_3992697 prefixEnd_3992697 227796963196074476480603 := by
  unfold tailWord_3992697
  simp only [CollatzResearch.WordTrace]
  refine ⟨145625623216148142204008345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97083748810765428136005563 145625623216148142204008345)
  ·
    refine ⟨109219217412111106653006259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145625623216148142204008345 109219217412111106653006259)
    ·
      refine ⟨163828826118166659979509389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109219217412111106653006259 163828826118166659979509389)
      ·
        refine ⟨61435809794312497492316021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163828826118166659979509389 61435809794312497492316021)
        ·
          refine ⟨5759607168216796639904627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61435809794312497492316021 5759607168216796639904627)
          ·
            refine ⟨8639410752325194959856941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759607168216796639904627 8639410752325194959856941)
            ·
              refine ⟨3239779032121948109946353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8639410752325194959856941 3239779032121948109946353)
              ·
                refine ⟨2429834274091461082459765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3239779032121948109946353 2429834274091461082459765)
                ·
                  refine ⟨227796963196074476480603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2429834274091461082459765 227796963196074476480603)
                  ·
                    rfl

theorem cell23_3992697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 5].length) (baseStart_3992697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992697 prefixEnd_3992697 := by exact prefixLift 3992697
  have htrace : WordTrace (prefixWord ++ tailWord_3992697) baseStart_3992697 baseEnd_3992697 := by
    simpa [prefixWord, tailWord_3992697, baseEnd_3992697] using wordTrace_append hprefix tailTrace_3992697
  have hstable : (prefixWord ++ tailWord_3992697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992697).length < 2 ^ (prefixWord ++ tailWord_3992697).sum := by decide
  have hdescent : baseEnd_3992697 < baseStart_3992697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992716 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3992716 : Nat := 118140960795 + 3992716 * 2 ^ 59
def prefixEnd_3992716 : Nat := 4983230072969 + 3 ^ 40 * 3992716 * 2
def baseEnd_3992716 : Nat := 2050182424897105713987839

theorem tailTrace_3992716 : CollatzResearch.WordTrace tailWord_3992716 prefixEnd_3992716 2050182424897105713987839 := by
  unfold tailWord_3992716
  simp only [CollatzResearch.WordTrace]
  refine ⟨72813158101539654224475001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97084210802052872299300001 72813158101539654224475001)
  ·
    refine ⟨54609868576154740668356251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72813158101539654224475001 54609868576154740668356251)
    ·
      refine ⟨81914802864232111002534377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54609868576154740668356251 81914802864232111002534377)
      ·
        refine ⟨61436102148174083251900783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81914802864232111002534377 61436102148174083251900783)
        ·
          refine ⟨92154153222261124877851175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61436102148174083251900783 92154153222261124877851175)
          ·
            refine ⟨138231229833391687316776763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92154153222261124877851175 138231229833391687316776763)
            ·
              refine ⟨207346844750087530975165145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138231229833391687316776763 207346844750087530975165145)
              ·
                refine ⟨155510133562565648231373859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207346844750087530975165145 155510133562565648231373859)
                ·
                  refine ⟨233265200343848472347060789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155510133562565648231373859 233265200343848472347060789)
                  ·
                    refine ⟨21868612532235794282536949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 233265200343848472347060789 21868612532235794282536949)
                    ·
                      refine ⟨2050182424897105713987839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21868612532235794282536949 2050182424897105713987839)
                      ·
                        rfl

theorem cell23_3992716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3992716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992716 prefixEnd_3992716 := by exact prefixLift 3992716
  have htrace : WordTrace (prefixWord ++ tailWord_3992716) baseStart_3992716 baseEnd_3992716 := by
    simpa [prefixWord, tailWord_3992716, baseEnd_3992716] using wordTrace_append hprefix tailTrace_3992716
  have hstable : (prefixWord ++ tailWord_3992716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992716).length < 2 ^ (prefixWord ++ tailWord_3992716).sum := by decide
  have hdescent : baseEnd_3992716 < baseStart_3992716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992723 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 3, 4]
def baseStart_3992723 : Nat := 118140960795 + 3992723 * 2 ^ 59
def prefixEnd_3992723 : Nat := 4983230072969 + 3 ^ 40 * 3992723 * 2
def baseEnd_3992723 : Nat := 683395339753895728866769

theorem tailTrace_3992723 : CollatzResearch.WordTrace tailWord_3992723 prefixEnd_3992723 683395339753895728866769 := by
  unfold tailWord_3992723
  simp only [CollatzResearch.WordTrace]
  refine ⟨145626571514053948644454823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97084381009369299096303215 145626571514053948644454823)
  ·
    refine ⟨218439857271080922966682235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145626571514053948644454823 218439857271080922966682235)
    ·
      refine ⟨327659785906621384450023353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218439857271080922966682235 327659785906621384450023353)
      ·
        refine ⟨245744839429966038337517515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327659785906621384450023353 245744839429966038337517515)
        ·
          refine ⟨368617259144949057506276273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245744839429966038337517515 368617259144949057506276273)
          ·
            refine ⟨276462944358711793129707205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368617259144949057506276273 276462944358711793129707205)
            ·
              refine ⟨51836802067258461211820101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276462944358711793129707205 51836802067258461211820101)
              ·
                refine ⟨9719400387610961477216269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51836802067258461211820101 9719400387610961477216269)
                ·
                  refine ⟨3644775145354110553956101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9719400387610961477216269 3644775145354110553956101)
                  ·
                    refine ⟨683395339753895728866769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3644775145354110553956101 683395339753895728866769)
                    ·
                      rfl

theorem cell23_3992723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 4].length) (baseStart_3992723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992723 prefixEnd_3992723 := by exact prefixLift 3992723
  have htrace : WordTrace (prefixWord ++ tailWord_3992723) baseStart_3992723 baseEnd_3992723 := by
    simpa [prefixWord, tailWord_3992723, baseEnd_3992723] using wordTrace_append hprefix tailTrace_3992723
  have hstable : (prefixWord ++ tailWord_3992723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992723).length < 2 ^ (prefixWord ++ tailWord_3992723).sum := by decide
  have hdescent : baseEnd_3992723 < baseStart_3992723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992730 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3992730 : Nat := 118140960795 + 3992730 * 2 ^ 59
def prefixEnd_3992730 : Nat := 4983230072969 + 3 ^ 40 * 3992730 * 2
def baseEnd_3992730 : Nat := 2050189613626268659212775

theorem tailTrace_3992730 : CollatzResearch.WordTrace tailWord_3992730 prefixEnd_3992730 2050189613626268659212775 := by
  unfold tailWord_3992730
  simp only [CollatzResearch.WordTrace]
  refine ⟨36406706706257147209989911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97084551216685725893306429 36406706706257147209989911)
  ·
    refine ⟨54610060059385720814984867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36406706706257147209989911 54610060059385720814984867)
    ·
      refine ⟨81915090089078581222477301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54610060059385720814984867 81915090089078581222477301)
      ·
        refine ⟨7679539695851116989607247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81915090089078581222477301 7679539695851116989607247)
        ·
          refine ⟨11519309543776675484410871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7679539695851116989607247 11519309543776675484410871)
          ·
            refine ⟨17278964315665013226616307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11519309543776675484410871 17278964315665013226616307)
            ·
              refine ⟨25918446473497519839924461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17278964315665013226616307 25918446473497519839924461)
              ·
                refine ⟨9719417427561569939971673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25918446473497519839924461 9719417427561569939971673)
                ·
                  refine ⟨7289563070671177454978755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9719417427561569939971673 7289563070671177454978755)
                  ·
                    refine ⟨10934344606006766182468133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7289563070671177454978755 10934344606006766182468133)
                    ·
                      refine ⟨2050189613626268659212775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10934344606006766182468133 2050189613626268659212775)
                      ·
                        rfl

theorem cell23_3992730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3992730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992730 prefixEnd_3992730 := by exact prefixLift 3992730
  have htrace : WordTrace (prefixWord ++ tailWord_3992730) baseStart_3992730 baseEnd_3992730 := by
    simpa [prefixWord, tailWord_3992730, baseEnd_3992730] using wordTrace_append hprefix tailTrace_3992730
  have hstable : (prefixWord ++ tailWord_3992730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992730).length < 2 ^ (prefixWord ++ tailWord_3992730).sum := by decide
  have hdescent : baseEnd_3992730 < baseStart_3992730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992781 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3992781 : Nat := 118140960795 + 3992781 * 2 ^ 59
def prefixEnd_3992781 : Nat := 4983230072969 + 3 ^ 40 * 3992781 * 2
def baseEnd_3992781 : Nat := 2050215801139647959675041

theorem tailTrace_3992781 : CollatzResearch.WordTrace tailWord_3992781 prefixEnd_3992781 2050215801139647959675041 := by
  unfold tailWord_3992781
  simp only [CollatzResearch.WordTrace]
  refine ⟨145628686947843824550066197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97085791298562549700044131 145628686947843824550066197)
  ·
    refine ⟨6826344700680179275784353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145628686947843824550066197 6826344700680179275784353)
    ·
      refine ⟨5119758525510134456838265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6826344700680179275784353 5119758525510134456838265)
      ·
        refine ⟨3839818894132600842628699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5119758525510134456838265 3839818894132600842628699)
        ·
          refine ⟨5759728341198901263943049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839818894132600842628699 5759728341198901263943049)
          ·
            refine ⟨4319796255899175947957287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5759728341198901263943049 4319796255899175947957287)
            ·
              refine ⟨6479694383848763921935931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319796255899175947957287 6479694383848763921935931)
              ·
                refine ⟨9719541575773145882903897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479694383848763921935931 9719541575773145882903897)
                ·
                  refine ⟨7289656181829859412177923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9719541575773145882903897 7289656181829859412177923)
                  ·
                    refine ⟨10934484272744789118266885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7289656181829859412177923 10934484272744789118266885)
                    ·
                      refine ⟨2050215801139647959675041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10934484272744789118266885 2050215801139647959675041)
                      ·
                        rfl

theorem cell23_3992781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3992781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992781 prefixEnd_3992781 := by exact prefixLift 3992781
  have htrace : WordTrace (prefixWord ++ tailWord_3992781) baseStart_3992781 baseEnd_3992781 := by
    simpa [prefixWord, tailWord_3992781, baseEnd_3992781] using wordTrace_append hprefix tailTrace_3992781
  have hstable : (prefixWord ++ tailWord_3992781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992781).length < 2 ^ (prefixWord ++ tailWord_3992781).sum := by decide
  have hdescent : baseEnd_3992781 < baseStart_3992781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992800 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_3992800 : Nat := 118140960795 + 3992800 * 2 ^ 59
def prefixEnd_3992800 : Nat := 4983230072969 + 3 ^ 40 * 3992800 * 2
def baseEnd_3992800 : Nat := 683408519090694461779151

theorem tailTrace_3992800 : CollatzResearch.WordTrace tailWord_3992800 prefixEnd_3992800 683408519090694461779151 := by
  unfold tailWord_3992800
  simp only [CollatzResearch.WordTrace]
  refine ⟨72814689967387495397503927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97086253289849993863338569 72814689967387495397503927)
  ·
    refine ⟨109222034951081243096255891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72814689967387495397503927 109222034951081243096255891)
    ·
      refine ⟨163833052426621864644383837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109222034951081243096255891 163833052426621864644383837)
      ·
        refine ⟨61437394659983199241643939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163833052426621864644383837 61437394659983199241643939)
        ·
          refine ⟨92156091989974798862465909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61437394659983199241643939 92156091989974798862465909)
          ·
            refine ⟨8639633624060137393356179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92156091989974798862465909 8639633624060137393356179)
            ·
              refine ⟨12959450436090206090034269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639633624060137393356179 12959450436090206090034269)
              ·
                refine ⟨4859793913533827283762851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12959450436090206090034269 4859793913533827283762851)
                ·
                  refine ⟨7289690870300740925644277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859793913533827283762851 7289690870300740925644277)
                  ·
                    refine ⟨683408519090694461779151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7289690870300740925644277 683408519090694461779151)
                    ·
                      rfl

theorem cell23_3992800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_3992800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992800 prefixEnd_3992800 := by exact prefixLift 3992800
  have htrace : WordTrace (prefixWord ++ tailWord_3992800) baseStart_3992800 baseEnd_3992800 := by
    simpa [prefixWord, tailWord_3992800, baseEnd_3992800] using wordTrace_append hprefix tailTrace_3992800
  have hstable : (prefixWord ++ tailWord_3992800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992800).length < 2 ^ (prefixWord ++ tailWord_3992800).sum := by decide
  have hdescent : baseEnd_3992800 < baseStart_3992800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992814 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_3992814 : Nat := 118140960795 + 3992814 * 2 ^ 59
def prefixEnd_3992814 : Nat := 4983230072969 + 3 ^ 40 * 3992814 * 2
def baseEnd_3992814 : Nat := 2050232746001246330562389

theorem tailTrace_3992814 : CollatzResearch.WordTrace tailWord_3992814 prefixEnd_3992814 2050232746001246330562389 := by
  unfold tailWord_3992814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18203736319590533898252187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97086593704482847457344997 18203736319590533898252187)
  ·
    refine ⟨27305604479385800847378281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18203736319590533898252187 27305604479385800847378281)
    ·
      refine ⟨20479203359539350635533711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27305604479385800847378281 20479203359539350635533711)
      ·
        refine ⟨30718805039309025953300567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20479203359539350635533711 30718805039309025953300567)
        ·
          refine ⟨46078207558963538929950851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30718805039309025953300567 46078207558963538929950851)
          ·
            refine ⟨69117311338445308394926277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46078207558963538929950851 69117311338445308394926277)
            ·
              refine ⟨12959495875958495324048677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69117311338445308394926277 12959495875958495324048677)
              ·
                refine ⟨2429905476742217873259127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12959495875958495324048677 2429905476742217873259127)
                ·
                  refine ⟨3644858215113326809888691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2429905476742217873259127 3644858215113326809888691)
                  ·
                    refine ⟨5467287322669990214833037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3644858215113326809888691 5467287322669990214833037)
                    ·
                      refine ⟨2050232746001246330562389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5467287322669990214833037 2050232746001246330562389)
                      ·
                        rfl

theorem cell23_3992814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_3992814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992814 prefixEnd_3992814 := by exact prefixLift 3992814
  have htrace : WordTrace (prefixWord ++ tailWord_3992814) baseStart_3992814 baseEnd_3992814 := by
    simpa [prefixWord, tailWord_3992814, baseEnd_3992814] using wordTrace_append hprefix tailTrace_3992814
  have hstable : (prefixWord ++ tailWord_3992814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992814).length < 2 ^ (prefixWord ++ tailWord_3992814).sum := by decide
  have hdescent : baseEnd_3992814 < baseStart_3992814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_3992823 : Nat := 118140960795 + 3992823 * 2 ^ 59
def prefixEnd_3992823 : Nat := 4983230072969 + 3 ^ 40 * 3992823 * 2
def baseEnd_3992823 : Nat := 2050237367327136795349847

theorem tailTrace_3992823 : CollatzResearch.WordTrace tailWord_3992823 prefixEnd_3992823 2050237367327136795349847 := by
  unfold tailWord_3992823
  simp only [CollatzResearch.WordTrace]
  refine ⟨145630218813691665723095123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97086812542461110482063415 145630218813691665723095123)
  ·
    refine ⟨218445328220537498584642685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145630218813691665723095123 218445328220537498584642685)
    ·
      refine ⟨81916998082701561969241007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218445328220537498584642685 81916998082701561969241007)
      ·
        refine ⟨122875497124052342953861511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81916998082701561969241007 122875497124052342953861511)
        ·
          refine ⟨184313245686078514430792267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122875497124052342953861511 184313245686078514430792267)
          ·
            refine ⟨276469868529117771646188401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184313245686078514430792267 276469868529117771646188401)
            ·
              refine ⟨207352401396838328734641301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276469868529117771646188401 207352401396838328734641301)
              ·
                refine ⟨9719643815476796659436311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207352401396838328734641301 9719643815476796659436311)
                ·
                  refine ⟨14579465723215194989154467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9719643815476796659436311 14579465723215194989154467)
                  ·
                    refine ⟨21869198584822792483731701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14579465723215194989154467 21869198584822792483731701)
                    ·
                      refine ⟨2050237367327136795349847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21869198584822792483731701 2050237367327136795349847)
                      ·
                        rfl

theorem cell23_3992823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_3992823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992823 prefixEnd_3992823 := by exact prefixLift 3992823
  have htrace : WordTrace (prefixWord ++ tailWord_3992823) baseStart_3992823 baseEnd_3992823 := by
    simpa [prefixWord, tailWord_3992823, baseEnd_3992823] using wordTrace_append hprefix tailTrace_3992823
  have hstable : (prefixWord ++ tailWord_3992823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992823).length < 2 ^ (prefixWord ++ tailWord_3992823).sum := by decide
  have hdescent : baseEnd_3992823 < baseStart_3992823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992834 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_3992834 : Nat := 118140960795 + 3992834 * 2 ^ 59
def prefixEnd_3992834 : Nat := 4983230072969 + 3 ^ 40 * 3992834 * 2
def baseEnd_3992834 : Nat := 683414338538112084104099

theorem tailTrace_3992834 : CollatzResearch.WordTrace tailWord_3992834 prefixEnd_3992834 683414338538112084104099 := by
  unfold tailWord_3992834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36407655004162953650436389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97087080011101209734497037 36407655004162953650436389)
  ·
    refine ⟨6826435313280553809456823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36407655004162953650436389 6826435313280553809456823)
    ·
      refine ⟨10239652969920830714185235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826435313280553809456823 10239652969920830714185235)
      ·
        refine ⟨15359479454881246071277853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10239652969920830714185235 15359479454881246071277853)
        ·
          refine ⟨5759804795580467276729195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15359479454881246071277853 5759804795580467276729195)
          ·
            refine ⟨8639707193370700915093793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5759804795580467276729195 8639707193370700915093793)
            ·
              refine ⟨6479780395028025686320345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639707193370700915093793 6479780395028025686320345)
              ·
                refine ⟨4859835296271019264740259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6479780395028025686320345 4859835296271019264740259)
                ·
                  refine ⟨7289752944406528897110389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4859835296271019264740259 7289752944406528897110389)
                  ·
                    refine ⟨683414338538112084104099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7289752944406528897110389 683414338538112084104099)
                    ·
                      rfl

theorem cell23_3992834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_3992834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992834 prefixEnd_3992834 := by exact prefixLift 3992834
  have htrace : WordTrace (prefixWord ++ tailWord_3992834) baseStart_3992834 baseEnd_3992834 := by
    simpa [prefixWord, tailWord_3992834, baseEnd_3992834] using wordTrace_append hprefix tailTrace_3992834
  have hstable : (prefixWord ++ tailWord_3992834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992834).length < 2 ^ (prefixWord ++ tailWord_3992834).sum := by decide
  have hdescent : baseEnd_3992834 < baseStart_3992834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992837 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_3992837 : Nat := 118140960795 + 3992837 * 2 ^ 59
def prefixEnd_3992837 : Nat := 4983230072969 + 3 ^ 40 * 3992837 * 2
def baseEnd_3992837 : Nat := 2050244556056299740574783

theorem tailTrace_3992837 : CollatzResearch.WordTrace tailWord_3992837 prefixEnd_3992837 2050244556056299740574783 := by
  unfold tailWord_3992837
  simp only [CollatzResearch.WordTrace]
  refine ⟨145630729435640946114104765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97087152957093964076069843 145630729435640946114104765)
  ·
    refine ⟨54611523538365354792789287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145630729435640946114104765 54611523538365354792789287)
    ·
      refine ⟨81917285307548032189183931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54611523538365354792789287 81917285307548032189183931)
      ·
        refine ⟨122875927961322048283775897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81917285307548032189183931 122875927961322048283775897)
        ·
          refine ⟨92156945970991536212831923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122875927961322048283775897 92156945970991536212831923)
          ·
            refine ⟨138235418956487304319247885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92156945970991536212831923 138235418956487304319247885)
            ·
              refine ⟨51838282108682739119717957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138235418956487304319247885 51838282108682739119717957)
              ·
                refine ⟨9719677895378013584947117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51838282108682739119717957 9719677895378013584947117)
                ·
                  refine ⟨3644879210766755094355169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9719677895378013584947117 3644879210766755094355169)
                  ·
                    refine ⟨2733659408075066320766377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644879210766755094355169 2733659408075066320766377)
                    ·
                      refine ⟨2050244556056299740574783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733659408075066320766377 2050244556056299740574783)
                      ·
                        rfl

theorem cell23_3992837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_3992837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992837 prefixEnd_3992837 := by exact prefixLift 3992837
  have htrace : WordTrace (prefixWord ++ tailWord_3992837) baseStart_3992837 baseEnd_3992837 := by
    simpa [prefixWord, tailWord_3992837, baseEnd_3992837] using wordTrace_append hprefix tailTrace_3992837
  have hstable : (prefixWord ++ tailWord_3992837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992837).length < 2 ^ (prefixWord ++ tailWord_3992837).sum := by decide
  have hdescent : baseEnd_3992837 < baseStart_3992837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992843 : List Nat := [1, 1, 1, 1, 5, 4, 1, 9]
def baseStart_3992843 : Nat := 118140960795 + 3992843 * 2 ^ 59
def prefixEnd_3992843 : Nat := 4983230072969 + 3 ^ 40 * 3992843 * 2
def baseEnd_3992843 : Nat := 75935097664452841374065

theorem tailTrace_3992843 : CollatzResearch.WordTrace tailWord_3992843 prefixEnd_3992843 75935097664452841374065 := by
  unfold tailWord_3992843
  simp only [CollatzResearch.WordTrace]
  refine ⟨145630948273619209138823183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97087298849079472759215455 145630948273619209138823183)
  ·
    refine ⟨218446422410428813708234775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145630948273619209138823183 218446422410428813708234775)
    ·
      refine ⟨327669633615643220562352163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218446422410428813708234775 327669633615643220562352163)
      ·
        refine ⟨491504450423464830843528245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327669633615643220562352163 491504450423464830843528245)
        ·
          refine ⟨46078542227199827891580773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 491504450423464830843528245 46078542227199827891580773)
          ·
            refine ⟨8639726667599967729671395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46078542227199827891580773 8639726667599967729671395)
            ·
              refine ⟨12959590001399951594507093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8639726667599967729671395 12959590001399951594507093)
              ·
                refine ⟨75935097664452841374065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12959590001399951594507093 75935097664452841374065)
                ·
                  rfl

theorem cell23_3992843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 9].length) (baseStart_3992843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992843 prefixEnd_3992843 := by exact prefixLift 3992843
  have htrace : WordTrace (prefixWord ++ tailWord_3992843) baseStart_3992843 baseEnd_3992843 := by
    simpa [prefixWord, tailWord_3992843, baseEnd_3992843] using wordTrace_append hprefix tailTrace_3992843
  have hstable : (prefixWord ++ tailWord_3992843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992843).length < 2 ^ (prefixWord ++ tailWord_3992843).sum := by decide
  have hdescent : baseEnd_3992843 < baseStart_3992843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992877 : List Nat := [1, 5, 3, 1, 1, 2, 2, 8]
def baseStart_3992877 : Nat := 118140960795 + 3992877 * 2 ^ 59
def prefixEnd_3992877 : Nat := 4983230072969 + 3 ^ 40 * 3992877 * 2
def baseEnd_3992877 : Nat := 75935744269721466076837

theorem tailTrace_3992877 : CollatzResearch.WordTrace tailWord_3992877 prefixEnd_3992877 75935744269721466076837 := by
  unfold tailWord_3992877
  simp only [CollatzResearch.WordTrace]
  refine ⟨145632188355496032945560885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97088125570330688630373923 145632188355496032945560885)
  ·
    refine ⟨13653017658327753088646333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145632188355496032945560885 13653017658327753088646333)
    ·
      refine ⟨5119881621872907408242375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13653017658327753088646333 5119881621872907408242375)
      ·
        refine ⟨7679822432809361112363563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5119881621872907408242375 7679822432809361112363563)
        ·
          refine ⟨11519733649214041668545345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7679822432809361112363563 11519733649214041668545345)
          ·
            refine ⟨8639800236910531251409009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11519733649214041668545345 8639800236910531251409009)
            ·
              refine ⟨6479850177682898438556757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8639800236910531251409009 6479850177682898438556757)
              ·
                refine ⟨75935744269721466076837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6479850177682898438556757 75935744269721466076837)
                ·
                  rfl

theorem cell23_3992877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 8].length) (baseStart_3992877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992877 prefixEnd_3992877 := by exact prefixLift 3992877
  have htrace : WordTrace (prefixWord ++ tailWord_3992877) baseStart_3992877 baseEnd_3992877 := by
    simpa [prefixWord, tailWord_3992877, baseEnd_3992877] using wordTrace_append hprefix tailTrace_3992877
  have hstable : (prefixWord ++ tailWord_3992877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992877).length < 2 ^ (prefixWord ++ tailWord_3992877).sum := by decide
  have hdescent : baseEnd_3992877 < baseStart_3992877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992940 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_3992940 : Nat := 118140960795 + 3992940 * 2 ^ 59
def prefixEnd_3992940 : Nat := 4983230072969 + 3 ^ 40 * 3992940 * 2
def baseEnd_3992940 : Nat := 2050297444563712837586809

theorem tailTrace_3992940 : CollatzResearch.WordTrace tailWord_3992940 prefixEnd_3992940 2050297444563712837586809 := by
  unfold tailWord_3992940
  simp only [CollatzResearch.WordTrace]
  refine ⟨72817243077133897352552137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97089657436178529803402849 72817243077133897352552137)
  ·
    refine ⟨54612932307850423014414103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72817243077133897352552137 54612932307850423014414103)
    ·
      refine ⟨81919398461775634521621155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54612932307850423014414103 81919398461775634521621155)
      ·
        refine ⟨122879097692663451782431733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81919398461775634521621155 122879097692663451782431733)
        ·
          refine ⟨11519915408687198604602975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122879097692663451782431733 11519915408687198604602975)
          ·
            refine ⟨17279873113030797906904463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11519915408687198604602975 17279873113030797906904463)
            ·
              refine ⟨25919809669546196860356695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17279873113030797906904463 25919809669546196860356695)
              ·
                refine ⟨38879714504319295290535043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25919809669546196860356695 38879714504319295290535043)
                ·
                  refine ⟨58319571756478942935802565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38879714504319295290535043 58319571756478942935802565)
                  ·
                    refine ⟨10934919704339801800462981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58319571756478942935802565 10934919704339801800462981)
                    ·
                      refine ⟨2050297444563712837586809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10934919704339801800462981 2050297444563712837586809)
                      ·
                        rfl

theorem cell23_3992940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_3992940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992940 prefixEnd_3992940 := by exact prefixLift 3992940
  have htrace : WordTrace (prefixWord ++ tailWord_3992940) baseStart_3992940 baseEnd_3992940 := by
    simpa [prefixWord, tailWord_3992940, baseEnd_3992940] using wordTrace_append hprefix tailTrace_3992940
  have hstable : (prefixWord ++ tailWord_3992940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992940).length < 2 ^ (prefixWord ++ tailWord_3992940).sum := by decide
  have hdescent : baseEnd_3992940 < baseStart_3992940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992944 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2]
def baseStart_3992944 : Nat := 118140960795 + 3992944 * 2 ^ 59
def prefixEnd_3992944 : Nat := 4983230072969 + 3 ^ 40 * 3992944 * 2
def baseEnd_3992944 : Nat := 2050299498486330821936791

theorem tailTrace_3992944 : CollatzResearch.WordTrace tailWord_3992944 prefixEnd_3992944 2050299498486330821936791 := by
  unfold tailWord_3992944
  simp only [CollatzResearch.WordTrace]
  refine ⟨72817316023126651694124943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97089754697502202258833257 72817316023126651694124943)
  ·
    refine ⟨109225974034689977541187415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72817316023126651694124943 109225974034689977541187415)
    ·
      refine ⟨163838961052034966311781123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109225974034689977541187415 163838961052034966311781123)
      ·
        refine ⟨245758441578052449467671685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163838961052034966311781123 245758441578052449467671685)
        ·
          refine ⟨46079707795884834275188441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245758441578052449467671685 46079707795884834275188441)
          ·
            refine ⟨34559780846913625706391331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46079707795884834275188441 34559780846913625706391331)
            ·
              refine ⟨51839671270370438559586997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34559780846913625706391331 51839671270370438559586997)
              ·
                refine ⟨4859969181597228614961281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51839671270370438559586997 4859969181597228614961281)
                ·
                  refine ⟨3644976886197921461220961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4859969181597228614961281 3644976886197921461220961)
                  ·
                    refine ⟨2733732664648441095915721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3644976886197921461220961 2733732664648441095915721)
                    ·
                      refine ⟨2050299498486330821936791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733732664648441095915721 2050299498486330821936791)
                      ·
                        rfl

theorem cell23_3992944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2].length) (baseStart_3992944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992944 prefixEnd_3992944 := by exact prefixLift 3992944
  have htrace : WordTrace (prefixWord ++ tailWord_3992944) baseStart_3992944 baseEnd_3992944 := by
    simpa [prefixWord, tailWord_3992944, baseEnd_3992944] using wordTrace_append hprefix tailTrace_3992944
  have hstable : (prefixWord ++ tailWord_3992944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992944).length < 2 ^ (prefixWord ++ tailWord_3992944).sum := by decide
  have hdescent : baseEnd_3992944 < baseStart_3992944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992967 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 5]
def baseStart_3992967 : Nat := 118140960795 + 3992967 * 2 ^ 59
def prefixEnd_3992967 : Nat := 4983230072969 + 3 ^ 40 * 3992967 * 2
def baseEnd_3992967 : Nat := 227812367615709359105465

theorem tailTrace_3992967 : CollatzResearch.WordTrace tailWord_3992967 prefixEnd_3992967 227812367615709359105465 := by
  unfold tailWord_3992967
  simp only [CollatzResearch.WordTrace]
  refine ⟨145635470925169978316337155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97090313950113318877558103 145635470925169978316337155)
  ·
    refine ⟨218453206387754967474505733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145635470925169978316337155 218453206387754967474505733)
    ·
      refine ⟨40959976197704056401469825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218453206387754967474505733 40959976197704056401469825)
      ·
        refine ⟨30719982148278042301102369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40959976197704056401469825 30719982148278042301102369)
        ·
          refine ⟨23039986611208531725826777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30719982148278042301102369 23039986611208531725826777)
          ·
            refine ⟨17279989958406398794370083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23039986611208531725826777 17279989958406398794370083)
            ·
              refine ⟨25919984937609598191555125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17279989958406398794370083 25919984937609598191555125)
              ·
                refine ⟨2429998587900899830458293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25919984937609598191555125 2429998587900899830458293)
                ·
                  refine ⟨227812367615709359105465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2429998587900899830458293 227812367615709359105465)
                  ·
                    rfl

theorem cell23_3992967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 5].length) (baseStart_3992967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992967 prefixEnd_3992967 := by exact prefixLift 3992967
  have htrace : WordTrace (prefixWord ++ tailWord_3992967) baseStart_3992967 baseEnd_3992967 := by
    simpa [prefixWord, tailWord_3992967, baseEnd_3992967] using wordTrace_append hprefix tailTrace_3992967
  have hstable : (prefixWord ++ tailWord_3992967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992967).length < 2 ^ (prefixWord ++ tailWord_3992967).sum := by decide
  have hdescent : baseEnd_3992967 < baseStart_3992967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3992978 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3992978 : Nat := 118140960795 + 3992978 * 2 ^ 59
def prefixEnd_3992978 : Nat := 4983230072969 + 3 ^ 40 * 3992978 * 2
def baseEnd_3992978 : Nat := 2050316956828583688911635

theorem tailTrace_3992978 : CollatzResearch.WordTrace tailWord_3992978 prefixEnd_3992978 2050316956828583688911635 := by
  unfold tailWord_3992978
  simp only [CollatzResearch.WordTrace]
  refine ⟨36408968032032531798746897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97090581418753418129991725 36408968032032531798746897)
  ·
    refine ⟨27306726024024398849060173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36408968032032531798746897 27306726024024398849060173)
    ·
      refine ⟨10240022259009149568397565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27306726024024398849060173 10240022259009149568397565)
      ·
        refine ⟨3840008347128431088149087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10240022259009149568397565 3840008347128431088149087)
        ·
          refine ⟨5760012520692646632223631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840008347128431088149087 5760012520692646632223631)
          ·
            refine ⟨8640018781038969948335447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760012520692646632223631 8640018781038969948335447)
            ·
              refine ⟨12960028171558454922503171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640018781038969948335447 12960028171558454922503171)
              ·
                refine ⟨19440042257337682383754757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12960028171558454922503171 19440042257337682383754757)
                ·
                  refine ⟨3645007923250815446954017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19440042257337682383754757 3645007923250815446954017)
                  ·
                    refine ⟨2733755942438111585215513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645007923250815446954017 2733755942438111585215513)
                    ·
                      refine ⟨2050316956828583688911635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733755942438111585215513 2050316956828583688911635)
                      ·
                        rfl

theorem cell23_3992978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3992978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3992978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3992978 prefixEnd_3992978 := by exact prefixLift 3992978
  have htrace : WordTrace (prefixWord ++ tailWord_3992978) baseStart_3992978 baseEnd_3992978 := by
    simpa [prefixWord, tailWord_3992978, baseEnd_3992978] using wordTrace_append hprefix tailTrace_3992978
  have hstable : (prefixWord ++ tailWord_3992978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3992978).length < 2 ^ (prefixWord ++ tailWord_3992978).sum := by decide
  have hdescent : baseEnd_3992978 < baseStart_3992978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3992978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993057 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 6]
def baseStart_3993057 : Nat := 118140960795 + 3993057 * 2 ^ 59
def prefixEnd_3993057 : Nat := 4983230072969 + 3 ^ 40 * 3993057 * 2
def baseEnd_3993057 : Nat := 227817502422254319980419

theorem tailTrace_3993057 : CollatzResearch.WordTrace tailWord_3993057 prefixEnd_3993057 227817502422254319980419 := by
  unfold tailWord_3993057
  simp only [CollatzResearch.WordTrace]
  refine ⟨145638753494843923687113425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97092502329895949124742283 145638753494843923687113425)
  ·
    refine ⟨109229065121132942765335069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145638753494843923687113425 109229065121132942765335069)
    ·
      refine ⟨40960899420424853537000651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109229065121132942765335069 40960899420424853537000651)
      ·
        refine ⟨61441349130637280305500977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40960899420424853537000651 61441349130637280305500977)
        ·
          refine ⟨46081011847977960229125733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61441349130637280305500977 46081011847977960229125733)
          ·
            refine ⟨8640189721495867542961075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46081011847977960229125733 8640189721495867542961075)
            ·
              refine ⟨12960284582243801314441613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640189721495867542961075 12960284582243801314441613)
              ·
                refine ⟨4860106718341425492915605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12960284582243801314441613 4860106718341425492915605)
                ·
                  refine ⟨227817502422254319980419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4860106718341425492915605 227817502422254319980419)
                  ·
                    rfl

theorem cell23_3993057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_3993057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993057 prefixEnd_3993057 := by exact prefixLift 3993057
  have htrace : WordTrace (prefixWord ++ tailWord_3993057) baseStart_3993057 baseEnd_3993057 := by
    simpa [prefixWord, tailWord_3993057, baseEnd_3993057] using wordTrace_append hprefix tailTrace_3993057
  have hstable : (prefixWord ++ tailWord_3993057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993057).length < 2 ^ (prefixWord ++ tailWord_3993057).sum := by decide
  have hdescent : baseEnd_3993057 < baseStart_3993057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993060 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3993060 : Nat := 118140960795 + 3993060 * 2 ^ 59
def prefixEnd_3993060 : Nat := 4983230072969 + 3 ^ 40 * 3993060 * 2
def baseEnd_3993060 : Nat := 2050359062242252368086257

theorem tailTrace_3993060 : CollatzResearch.WordTrace tailWord_3993060 prefixEnd_3993060 2050359062242252368086257 := by
  unfold tailWord_3993060
  simp only [CollatzResearch.WordTrace]
  refine ⟨72819431456916527599736317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97092575275888703466315089 72819431456916527599736317)
  ·
    refine ⟨27307286796343697849901119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72819431456916527599736317 27307286796343697849901119)
    ·
      refine ⟨40960930194515546774851679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27307286796343697849901119 40960930194515546774851679)
      ·
        refine ⟨61441395291773320162277519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40960930194515546774851679 61441395291773320162277519)
        ·
          refine ⟨92162092937659980243416279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61441395291773320162277519 92162092937659980243416279)
          ·
            refine ⟨138243139406489970365124419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92162092937659980243416279 138243139406489970365124419)
            ·
              refine ⟨207364709109734955547686629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138243139406489970365124419 207364709109734955547686629)
              ·
                refine ⟨38880882958075304165191243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207364709109734955547686629 38880882958075304165191243)
                ·
                  refine ⟨58321324437112956247786865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38880882958075304165191243 58321324437112956247786865)
                  ·
                    refine ⟨43740993327834717185840149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58321324437112956247786865 43740993327834717185840149)
                    ·
                      refine ⟨2050359062242252368086257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43740993327834717185840149 2050359062242252368086257)
                      ·
                        rfl

theorem cell23_3993060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3993060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993060 prefixEnd_3993060 := by exact prefixLift 3993060
  have htrace : WordTrace (prefixWord ++ tailWord_3993060) baseStart_3993060 baseEnd_3993060 := by
    simpa [prefixWord, tailWord_3993060, baseEnd_3993060] using wordTrace_append hprefix tailTrace_3993060
  have hstable : (prefixWord ++ tailWord_3993060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993060).length < 2 ^ (prefixWord ++ tailWord_3993060).sum := by decide
  have hdescent : baseEnd_3993060 < baseStart_3993060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993107 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4]
def baseStart_3993107 : Nat := 118140960795 + 3993107 * 2 ^ 59
def prefixEnd_3993107 : Nat := 4983230072969 + 3 ^ 40 * 3993107 * 2
def baseEnd_3993107 : Nat := 2050383195833013684198541

theorem tailTrace_3993107 : CollatzResearch.WordTrace tailWord_3993107 prefixEnd_3993107 2050383195833013684198541 := by
  unfold tailWord_3993107
  simp only [CollatzResearch.WordTrace]
  refine ⟨145640577144662782226433575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97093718096441854817622383 145640577144662782226433575)
  ·
    refine ⟨218460865716994173339650363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145640577144662782226433575 218460865716994173339650363)
    ·
      refine ⟨327691298575491260009475545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218460865716994173339650363 327691298575491260009475545)
      ·
        refine ⟨245768473931618445007106659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327691298575491260009475545 245768473931618445007106659)
        ·
          refine ⟨368652710897427667510659989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245768473931618445007106659 368652710897427667510659989)
          ·
            refine ⟨17280595823316921914562187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 368652710897427667510659989 17280595823316921914562187)
            ·
              refine ⟨25920893734975382871843281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280595823316921914562187 25920893734975382871843281)
              ·
                refine ⟨19440670301231537153882461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25920893734975382871843281 19440670301231537153882461)
                ·
                  refine ⟨7290251362961826432705923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19440670301231537153882461 7290251362961826432705923)
                  ·
                    refine ⟨10935377044442739649058885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7290251362961826432705923 10935377044442739649058885)
                    ·
                      refine ⟨2050383195833013684198541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10935377044442739649058885 2050383195833013684198541)
                      ·
                        rfl

theorem cell23_3993107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_3993107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993107 prefixEnd_3993107 := by exact prefixLift 3993107
  have htrace : WordTrace (prefixWord ++ tailWord_3993107) baseStart_3993107 baseEnd_3993107 := by
    simpa [prefixWord, tailWord_3993107, baseEnd_3993107] using wordTrace_append hprefix tailTrace_3993107
  have hstable : (prefixWord ++ tailWord_3993107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993107).length < 2 ^ (prefixWord ++ tailWord_3993107).sum := by decide
  have hdescent : baseEnd_3993107 < baseStart_3993107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993134 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3993134 : Nat := 118140960795 + 3993134 * 2 ^ 59
def prefixEnd_3993134 : Nat := 4983230072969 + 3 ^ 40 * 3993134 * 2
def baseEnd_3993134 : Nat := 683465686603561692853639

theorem tailTrace_3993134 : CollatzResearch.WordTrace tailWord_3993134 prefixEnd_3993134 683465686603561692853639 := by
  unfold tailWord_3993134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18205195239445620729708307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97094374610376643891777637 18205195239445620729708307)
  ·
    refine ⟨27307792859168431094562461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18205195239445620729708307 27307792859168431094562461)
    ·
      refine ⟨10240422322188161660460923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27307792859168431094562461 10240422322188161660460923)
      ·
        refine ⟨15360633483282242490691385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240422322188161660460923 15360633483282242490691385)
        ·
          refine ⟨11520475112461681868018539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15360633483282242490691385 11520475112461681868018539)
          ·
            refine ⟨17280712668692522802027809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520475112461681868018539 17280712668692522802027809)
            ·
              refine ⟨12960534501519392101520857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17280712668692522802027809 12960534501519392101520857)
              ·
                refine ⟨9720400876139544076140643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12960534501519392101520857 9720400876139544076140643)
                ·
                  refine ⟨14580601314209316114210965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9720400876139544076140643 14580601314209316114210965)
                  ·
                    refine ⟨683465686603561692853639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14580601314209316114210965 683465686603561692853639)
                    ·
                      rfl

theorem cell23_3993134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3993134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993134 prefixEnd_3993134 := by exact prefixLift 3993134
  have htrace : WordTrace (prefixWord ++ tailWord_3993134) baseStart_3993134 baseEnd_3993134 := by
    simpa [prefixWord, tailWord_3993134, baseEnd_3993134] using wordTrace_append hprefix tailTrace_3993134
  have hstable : (prefixWord ++ tailWord_3993134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993134).length < 2 ^ (prefixWord ++ tailWord_3993134).sum := by decide
  have hdescent : baseEnd_3993134 < baseStart_3993134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993141 : List Nat := [1, 3, 3, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_3993141 : Nat := 118140960795 + 3993141 * 2 ^ 59
def prefixEnd_3993141 : Nat := 4983230072969 + 3 ^ 40 * 3993141 * 2
def baseEnd_3993141 : Nat := 2050400654175266551173385

theorem tailTrace_3993141 : CollatzResearch.WordTrace tailWord_3993141 prefixEnd_3993141 2050400654175266551173385 := by
  unfold tailWord_3993141
  simp only [CollatzResearch.WordTrace]
  refine ⟨145641817226539606033171277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97094544817693070688780851 145641817226539606033171277)
  ·
    refine ⟨54615681459952352262439229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145641817226539606033171277 54615681459952352262439229)
    ·
      refine ⟨20480880547482132098414711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54615681459952352262439229 20480880547482132098414711)
      ·
        refine ⟨30721320821223198147622067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20480880547482132098414711 30721320821223198147622067)
        ·
          refine ⟨46081981231834797221433101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30721320821223198147622067 46081981231834797221433101)
          ·
            refine ⟨17280742961938048958037413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46081981231834797221433101 17280742961938048958037413)
            ·
              refine ⟨3240139305363384179632015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17280742961938048958037413 3240139305363384179632015)
              ·
                refine ⟨4860208958045076269448023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240139305363384179632015 4860208958045076269448023)
                ·
                  refine ⟨7290313437067614404172035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4860208958045076269448023 7290313437067614404172035)
                  ·
                    refine ⟨10935470155601421606258053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7290313437067614404172035 10935470155601421606258053)
                    ·
                      refine ⟨2050400654175266551173385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10935470155601421606258053 2050400654175266551173385)
                      ·
                        rfl

theorem cell23_3993141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_3993141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993141 prefixEnd_3993141 := by exact prefixLift 3993141
  have htrace : WordTrace (prefixWord ++ tailWord_3993141) baseStart_3993141 baseEnd_3993141 := by
    simpa [prefixWord, tailWord_3993141, baseEnd_3993141] using wordTrace_append hprefix tailTrace_3993141
  have hstable : (prefixWord ++ tailWord_3993141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993141).length < 2 ^ (prefixWord ++ tailWord_3993141).sum := by decide
  have hdescent : baseEnd_3993141 < baseStart_3993141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993151 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 2, 4]
def baseStart_3993151 : Nat := 118140960795 + 3993151 * 2 ^ 59
def prefixEnd_3993151 : Nat := 4983230072969 + 3 ^ 40 * 3993151 * 2
def baseEnd_3993151 : Nat := 683468596327270504016113

theorem tailTrace_3993151 : CollatzResearch.WordTrace tailWord_3993151 prefixEnd_3993151 683468596327270504016113 := by
  unfold tailWord_3993151
  simp only [CollatzResearch.WordTrace]
  refine ⟨145642181956503377741035307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97094787971002251827356871 145642181956503377741035307)
  ·
    refine ⟨218463272934755066611552961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145642181956503377741035307 218463272934755066611552961)
    ·
      refine ⟨163847454701066299958664721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218463272934755066611552961 163847454701066299958664721)
      ·
        refine ⟨122885591025799724968998541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163847454701066299958664721 122885591025799724968998541)
        ·
          refine ⟨46082096634674896863374453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122885591025799724968998541 46082096634674896863374453)
          ·
            refine ⟨4320196559500771580941355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46082096634674896863374453 4320196559500771580941355)
            ·
              refine ⟨6480294839251157371412033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320196559500771580941355 6480294839251157371412033)
              ·
                refine ⟨4860221129438368028559025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480294839251157371412033 4860221129438368028559025)
                ·
                  refine ⟨3645165847078776021419269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860221129438368028559025 3645165847078776021419269)
                  ·
                    refine ⟨683468596327270504016113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645165847078776021419269 683468596327270504016113)
                    ·
                      rfl

theorem cell23_3993151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_3993151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993151 prefixEnd_3993151 := by exact prefixLift 3993151
  have htrace : WordTrace (prefixWord ++ tailWord_3993151) baseStart_3993151 baseEnd_3993151 := by
    simpa [prefixWord, tailWord_3993151, baseEnd_3993151] using wordTrace_append hprefix tailTrace_3993151
  have hstable : (prefixWord ++ tailWord_3993151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993151).length < 2 ^ (prefixWord ++ tailWord_3993151).sum := by decide
  have hdescent : baseEnd_3993151 < baseStart_3993151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993181 : List Nat := [1, 4, 4, 2, 1, 1, 1, 9]
def baseStart_3993181 : Nat := 118140960795 + 3993181 * 2 ^ 59
def prefixEnd_3993181 : Nat := 4983230072969 + 3 ^ 40 * 3993181 * 2
def baseEnd_3993181 : Nat := 75941525681535051654563

theorem tailTrace_3993181 : CollatzResearch.WordTrace tailWord_3993181 prefixEnd_3993181 75941525681535051654563 := by
  unfold tailWord_3993181
  simp only [CollatzResearch.WordTrace]
  refine ⟨145643276146394692864627397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97095517430929795243084931 145643276146394692864627397)
  ·
    refine ⟨27308114277449004912117637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145643276146394692864627397 27308114277449004912117637)
    ·
      refine ⟨5120271427021688421022057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27308114277449004912117637 5120271427021688421022057)
      ·
        refine ⟨3840203570266266315766543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5120271427021688421022057 3840203570266266315766543)
        ·
          refine ⟨5760305355399399473649815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3840203570266266315766543 5760305355399399473649815)
          ·
            refine ⟨8640458033099099210474723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760305355399399473649815 8640458033099099210474723)
            ·
              refine ⟨12960687049648648815712085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640458033099099210474723 12960687049648648815712085)
              ·
                refine ⟨75941525681535051654563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12960687049648648815712085 75941525681535051654563)
                ·
                  rfl

theorem cell23_3993181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 9].length) (baseStart_3993181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993181 prefixEnd_3993181 := by exact prefixLift 3993181
  have htrace : WordTrace (prefixWord ++ tailWord_3993181) baseStart_3993181 baseEnd_3993181 := by
    simpa [prefixWord, tailWord_3993181, baseEnd_3993181] using wordTrace_append hprefix tailTrace_3993181
  have hstable : (prefixWord ++ tailWord_3993181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993181).length < 2 ^ (prefixWord ++ tailWord_3993181).sum := by decide
  have hdescent : baseEnd_3993181 < baseStart_3993181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993187 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3993187 : Nat := 118140960795 + 3993187 * 2 ^ 59
def prefixEnd_3993187 : Nat := 4983230072969 + 3 ^ 40 * 3993187 * 2
def baseEnd_3993187 : Nat := 2050424274285373371198173

theorem tailTrace_3993187 : CollatzResearch.WordTrace tailWord_3993187 prefixEnd_3993187 2050424274285373371198173 := by
  unfold tailWord_3993187
  simp only [CollatzResearch.WordTrace]
  refine ⟨145643494984372955889345815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97095663322915303926230543 145643494984372955889345815)
  ·
    refine ⟨218465242476559433834018723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145643494984372955889345815 218465242476559433834018723)
    ·
      refine ⟨327697863714839150751028085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218465242476559433834018723 327697863714839150751028085)
      ·
        refine ⟨30721674723266170382908883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327697863714839150751028085 30721674723266170382908883)
        ·
          refine ⟨46082512084899255574363325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30721674723266170382908883 46082512084899255574363325)
          ·
            refine ⟨17280942031837220840386247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46082512084899255574363325 17280942031837220840386247)
            ·
              refine ⟨25921413047755831260579371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280942031837220840386247 25921413047755831260579371)
              ·
                refine ⟨38882119571633746890869057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25921413047755831260579371 38882119571633746890869057)
                ·
                  refine ⟨29161589678725310168151793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38882119571633746890869057 29161589678725310168151793)
                  ·
                    refine ⟨21871192259043982626113845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29161589678725310168151793 21871192259043982626113845)
                    ·
                      refine ⟨2050424274285373371198173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21871192259043982626113845 2050424274285373371198173)
                      ·
                        rfl

theorem cell23_3993187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3993187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993187 prefixEnd_3993187 := by exact prefixLift 3993187
  have htrace : WordTrace (prefixWord ++ tailWord_3993187) baseStart_3993187 baseEnd_3993187 := by
    simpa [prefixWord, tailWord_3993187, baseEnd_3993187] using wordTrace_append hprefix tailTrace_3993187
  have hstable : (prefixWord ++ tailWord_3993187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993187).length < 2 ^ (prefixWord ++ tailWord_3993187).sum := by decide
  have hdescent : baseEnd_3993187 < baseStart_3993187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993192 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3993192 : Nat := 118140960795 + 3993192 * 2 ^ 59
def prefixEnd_3993192 : Nat := 4983230072969 + 3 ^ 40 * 3993192 * 2
def baseEnd_3993192 : Nat := 2050426841688645851635651

theorem tailTrace_3993192 : CollatzResearch.WordTrace tailWord_3993192 prefixEnd_3993192 2050426841688645851635651 := by
  unfold tailWord_3993192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72821838674677420871638915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97095784899569894495518553 72821838674677420871638915)
  ·
    refine ⟨109232758012016131307458373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72821838674677420871638915 109232758012016131307458373)
    ·
      refine ⟨20481142127253024620148445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109232758012016131307458373 20481142127253024620148445)
      ·
        refine ⟨7680428297719884232555667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20481142127253024620148445 7680428297719884232555667)
        ·
          refine ⟨11520642446579826348833501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7680428297719884232555667 11520642446579826348833501)
          ·
            refine ⟨4320240917467434880812563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11520642446579826348833501 4320240917467434880812563)
            ·
              refine ⟨6480361376201152321218845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320240917467434880812563 6480361376201152321218845)
              ·
                refine ⟨2430135516075432120457067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480361376201152321218845 2430135516075432120457067)
                ·
                  refine ⟨3645203274113148180685601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430135516075432120457067 3645203274113148180685601)
                  ·
                    refine ⟨2733902455584861135514201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645203274113148180685601 2733902455584861135514201)
                    ·
                      refine ⟨2050426841688645851635651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2733902455584861135514201 2050426841688645851635651)
                      ·
                        rfl

theorem cell23_3993192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3993192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993192 prefixEnd_3993192 := by exact prefixLift 3993192
  have htrace : WordTrace (prefixWord ++ tailWord_3993192) baseStart_3993192 baseEnd_3993192 := by
    simpa [prefixWord, tailWord_3993192, baseEnd_3993192] using wordTrace_append hprefix tailTrace_3993192
  have hstable : (prefixWord ++ tailWord_3993192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993192).length < 2 ^ (prefixWord ++ tailWord_3993192).sum := by decide
  have hdescent : baseEnd_3993192 < baseStart_3993192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993227 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_3993227 : Nat := 118140960795 + 3993227 * 2 ^ 59
def prefixEnd_3993227 : Nat := 4983230072969 + 3 ^ 40 * 3993227 * 2
def baseEnd_3993227 : Nat := 2050444813511553214697989

theorem tailTrace_3993227 : CollatzResearch.WordTrace tailWord_3993227 prefixEnd_3993227 2050444813511553214697989 := by
  unfold tailWord_3993227
  simp only [CollatzResearch.WordTrace]
  refine ⟨145644953904228042720801935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97096635936152028480534623 145644953904228042720801935)
  ·
    refine ⟨218467430856342064081202903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145644953904228042720801935 218467430856342064081202903)
    ·
      refine ⟨327701146284513096121804355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218467430856342064081202903 327701146284513096121804355)
      ·
        refine ⟨491551719426769644182706533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327701146284513096121804355 491551719426769644182706533)
        ·
          refine ⟨92165947392519308284257475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 491551719426769644182706533 92165947392519308284257475)
          ·
            refine ⟨138248921088778962426386213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92165947392519308284257475 138248921088778962426386213)
            ·
              refine ⟨25921672704146055454947415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138248921088778962426386213 25921672704146055454947415)
              ·
                refine ⟨38882509056219083182421123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25921672704146055454947415 38882509056219083182421123)
                ·
                  refine ⟨58323763584328624773631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38882509056219083182421123 58323763584328624773631685)
                  ·
                    refine ⟨10935705672061617145055941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58323763584328624773631685 10935705672061617145055941)
                    ·
                      refine ⟨2050444813511553214697989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10935705672061617145055941 2050444813511553214697989)
                      ·
                        rfl

theorem cell23_3993227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_3993227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993227 prefixEnd_3993227 := by exact prefixLift 3993227
  have htrace : WordTrace (prefixWord ++ tailWord_3993227) baseStart_3993227 baseEnd_3993227 := by
    simpa [prefixWord, tailWord_3993227, baseEnd_3993227] using wordTrace_append hprefix tailTrace_3993227
  have hstable : (prefixWord ++ tailWord_3993227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993227).length < 2 ^ (prefixWord ++ tailWord_3993227).sum := by decide
  have hdescent : baseEnd_3993227 < baseStart_3993227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993237 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 7]
def baseStart_3993237 : Nat := 118140960795 + 3993237 * 2 ^ 59
def prefixEnd_3993237 : Nat := 4983230072969 + 3 ^ 40 * 3993237 * 2
def baseEnd_3993237 : Nat := 227827772035344241730327

theorem tailTrace_3993237 : CollatzResearch.WordTrace tailWord_3993237 prefixEnd_3993237 227827772035344241730327 := by
  unfold tailWord_3993237
  simp only [CollatzResearch.WordTrace]
  refine ⟨145645318634191814428665965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97096879089461209619110643 145645318634191814428665965)
  ·
    refine ⟨54616994487821930410749737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145645318634191814428665965 54616994487821930410749737)
    ·
      refine ⟨40962745865866447808062303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54616994487821930410749737 40962745865866447808062303)
      ·
        refine ⟨61444118798799671712093455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40962745865866447808062303 61444118798799671712093455)
        ·
          refine ⟨92166178198199507568140183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61444118798799671712093455 92166178198199507568140183)
          ·
            refine ⟨138249267297299261352210275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92166178198199507568140183 138249267297299261352210275)
            ·
              refine ⟨207373900945948892028315413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138249267297299261352210275 207373900945948892028315413)
              ·
                refine ⟨9720651606841354313827285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 207373900945948892028315413 9720651606841354313827285)
                ·
                  refine ⟨227827772035344241730327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9720651606841354313827285 227827772035344241730327)
                  ·
                    rfl

theorem cell23_3993237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_3993237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993237 prefixEnd_3993237 := by exact prefixLift 3993237
  have htrace : WordTrace (prefixWord ++ tailWord_3993237) baseStart_3993237 baseEnd_3993237 := by
    simpa [prefixWord, tailWord_3993237, baseEnd_3993237] using wordTrace_append hprefix tailTrace_3993237
  have hstable : (prefixWord ++ tailWord_3993237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993237).length < 2 ^ (prefixWord ++ tailWord_3993237).sum := by decide
  have hdescent : baseEnd_3993237 < baseStart_3993237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993271 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 5]
def baseStart_3993271 : Nat := 118140960795 + 3993271 * 2 ^ 59
def prefixEnd_3993271 : Nat := 4983230072969 + 3 ^ 40 * 3993271 * 2
def baseEnd_3993271 : Nat := 227829711851150115838643

theorem tailTrace_3993271 : CollatzResearch.WordTrace tailWord_3993271 prefixEnd_3993271 227829711851150115838643 := by
  unfold tailWord_3993271
  simp only [CollatzResearch.WordTrace]
  refine ⟨145646558716068638235403667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97097705810712425490269111 145646558716068638235403667)
  ·
    refine ⟨218469838074102957353105501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145646558716068638235403667 218469838074102957353105501)
    ·
      refine ⟨81926189277788609007414563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218469838074102957353105501 81926189277788609007414563)
      ·
        refine ⟨122889283916682913511121845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81926189277788609007414563 122889283916682913511121845)
        ·
          refine ⟨11520870367189023141667673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122889283916682913511121845 11520870367189023141667673)
          ·
            refine ⟨8640652775391767356250755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11520870367189023141667673 8640652775391767356250755)
            ·
              refine ⟨12960979163087651034376133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640652775391767356250755 12960979163087651034376133)
              ·
                refine ⟨2430183593078934568945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12960979163087651034376133 2430183593078934568945525)
                ·
                  refine ⟨227829711851150115838643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2430183593078934568945525 227829711851150115838643)
                  ·
                    rfl

theorem cell23_3993271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 5].length) (baseStart_3993271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993271 prefixEnd_3993271 := by exact prefixLift 3993271
  have htrace : WordTrace (prefixWord ++ tailWord_3993271) baseStart_3993271 baseEnd_3993271 := by
    simpa [prefixWord, tailWord_3993271, baseEnd_3993271] using wordTrace_append hprefix tailTrace_3993271
  have hstable : (prefixWord ++ tailWord_3993271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993271).length < 2 ^ (prefixWord ++ tailWord_3993271).sum := by decide
  have hdescent : baseEnd_3993271 < baseStart_3993271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993284 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3993284 : Nat := 118140960795 + 3993284 * 2 ^ 59
def prefixEnd_3993284 : Nat := 4983230072969 + 3 ^ 40 * 3993284 * 2
def baseEnd_3993284 : Nat := 683491360636286497228409

theorem tailTrace_3993284 : CollatzResearch.WordTrace tailWord_3993284 prefixEnd_3993284 683491360636286497228409 := by
  unfold tailWord_3993284
  simp only [CollatzResearch.WordTrace]
  refine ⟨72823516432510770727813453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97098021910014360970417937 72823516432510770727813453)
  ·
    refine ⟨27308818662191539022930045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72823516432510770727813453 27308818662191539022930045)
    ·
      refine ⟨10240806998321827133598767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27308818662191539022930045 10240806998321827133598767)
      ·
        refine ⟨15361210497482740700398151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10240806998321827133598767 15361210497482740700398151)
        ·
          refine ⟨23041815746224111050597227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15361210497482740700398151 23041815746224111050597227)
          ·
            refine ⟨34562723619336166575895841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23041815746224111050597227 34562723619336166575895841)
            ·
              refine ⟨25922042714502124931921881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34562723619336166575895841 25922042714502124931921881)
              ·
                refine ⟨19441532035876593698941411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25922042714502124931921881 19441532035876593698941411)
                ·
                  refine ⟨29162298053814890548412117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19441532035876593698941411 29162298053814890548412117)
                  ·
                    refine ⟨683491360636286497228409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29162298053814890548412117 683491360636286497228409)
                    ·
                      rfl

theorem cell23_3993284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3993284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993284 prefixEnd_3993284 := by exact prefixLift 3993284
  have htrace : WordTrace (prefixWord ++ tailWord_3993284) baseStart_3993284 baseEnd_3993284 := by
    simpa [prefixWord, tailWord_3993284, baseEnd_3993284] using wordTrace_append hprefix tailTrace_3993284
  have hstable : (prefixWord ++ tailWord_3993284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993284).length < 2 ^ (prefixWord ++ tailWord_3993284).sum := by decide
  have hdescent : baseEnd_3993284 < baseStart_3993284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993304 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3993304 : Nat := 118140960795 + 3993304 * 2 ^ 59
def prefixEnd_3993304 : Nat := 4983230072969 + 3 ^ 40 * 3993304 * 2
def baseEnd_3993304 : Nat := 2050484351521949413435135

theorem tailTrace_3993304 : CollatzResearch.WordTrace tailWord_3993304 prefixEnd_3993304 2050484351521949413435135 := by
  unfold tailWord_3993304
  simp only [CollatzResearch.WordTrace]
  refine ⟨72823881162474542435677483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97098508216632723247569977 72823881162474542435677483)
  ·
    refine ⟨109235821743711813653516225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72823881162474542435677483 109235821743711813653516225)
    ·
      refine ⟨81926866307783860240137169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109235821743711813653516225 81926866307783860240137169)
      ·
        refine ⟨61445149730837895180102877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81926866307783860240137169 61445149730837895180102877)
        ·
          refine ⟨23041931149064210692538579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61445149730837895180102877 23041931149064210692538579)
          ·
            refine ⟨34562896723596316038807869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23041931149064210692538579 34562896723596316038807869)
            ·
              refine ⟨12961086271348618514552951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34562896723596316038807869 12961086271348618514552951)
              ·
                refine ⟨19441629407022927771829427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12961086271348618514552951 19441629407022927771829427)
                ·
                  refine ⟨29162444110534391657744141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19441629407022927771829427 29162444110534391657744141)
                  ·
                    refine ⟨10935916541450396871654053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29162444110534391657744141 10935916541450396871654053)
                    ·
                      refine ⟨2050484351521949413435135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10935916541450396871654053 2050484351521949413435135)
                      ·
                        rfl

theorem cell23_3993304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3993304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993304 prefixEnd_3993304 := by exact prefixLift 3993304
  have htrace : WordTrace (prefixWord ++ tailWord_3993304) baseStart_3993304 baseEnd_3993304 := by
    simpa [prefixWord, tailWord_3993304, baseEnd_3993304] using wordTrace_append hprefix tailTrace_3993304
  have hstable : (prefixWord ++ tailWord_3993304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993304).length < 2 ^ (prefixWord ++ tailWord_3993304).sum := by decide
  have hdescent : baseEnd_3993304 < baseStart_3993304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993365 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_3993365 : Nat := 118140960795 + 3993365 * 2 ^ 59
def prefixEnd_3993365 : Nat := 4983230072969 + 3 ^ 40 * 3993365 * 2
def baseEnd_3993365 : Nat := 683505224613957891590785

theorem tailTrace_3993365 : CollatzResearch.WordTrace tailWord_3993365 prefixEnd_3993365 683505224613957891590785 := by
  unfold tailWord_3993365
  simp only [CollatzResearch.WordTrace]
  refine ⟨145649987177728092289325549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97099991451818728192883699 145649987177728092289325549)
  ·
    refine ⟨54618745191648034608497081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145649987177728092289325549 54618745191648034608497081)
    ·
      refine ⟨40964058893736025956372811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54618745191648034608497081 40964058893736025956372811)
      ·
        refine ⟨61446088340604038934559217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40964058893736025956372811 61446088340604038934559217)
        ·
          refine ⟨46084566255453029200919413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61446088340604038934559217 46084566255453029200919413)
          ·
            refine ⟨4320428086448721487586195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46084566255453029200919413 4320428086448721487586195)
            ·
              refine ⟨6480642129673082231379293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320428086448721487586195 6480642129673082231379293)
              ·
                refine ⟨2430240798627405836767235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480642129673082231379293 2430240798627405836767235)
                ·
                  refine ⟨3645361197941108755150853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430240798627405836767235 3645361197941108755150853)
                  ·
                    refine ⟨683505224613957891590785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645361197941108755150853 683505224613957891590785)
                    ·
                      rfl

theorem cell23_3993365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_3993365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993365 prefixEnd_3993365 := by exact prefixLift 3993365
  have htrace : WordTrace (prefixWord ++ tailWord_3993365) baseStart_3993365 baseEnd_3993365 := by
    simpa [prefixWord, tailWord_3993365, baseEnd_3993365] using wordTrace_append hprefix tailTrace_3993365
  have hstable : (prefixWord ++ tailWord_3993365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993365).length < 2 ^ (prefixWord ++ tailWord_3993365).sum := by decide
  have hdescent : baseEnd_3993365 < baseStart_3993365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993388 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_3993388 : Nat := 118140960795 + 3993388 * 2 ^ 59
def prefixEnd_3993388 : Nat := 4983230072969 + 3 ^ 40 * 3993388 * 2
def baseEnd_3993388 : Nat := 2050527483896927084784749

theorem tailTrace_3993388 : CollatzResearch.WordTrace tailWord_3993388 prefixEnd_3993388 2050527483896927084784749 := by
  unfold tailWord_3993388
  simp only [CollatzResearch.WordTrace]
  refine ⟨72825413028322383608706409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97100550704429844811608545 72825413028322383608706409)
  ·
    refine ⟨54619059771241787706529807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72825413028322383608706409 54619059771241787706529807)
    ·
      refine ⟨81928589656862681559794711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54619059771241787706529807 81928589656862681559794711)
      ·
        refine ⟨122892884485294022339692067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81928589656862681559794711 122892884485294022339692067)
        ·
          refine ⟨184339326727941033509538101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122892884485294022339692067 184339326727941033509538101)
          ·
            refine ⟨17281811880744471891519197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184339326727941033509538101 17281811880744471891519197)
            ·
              refine ⟨6480679455279176959319699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17281811880744471891519197 6480679455279176959319699)
              ·
                refine ⟨9721019182918765438979549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6480679455279176959319699 9721019182918765438979549)
                ·
                  refine ⟨3645382193594537039617331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9721019182918765438979549 3645382193594537039617331)
                  ·
                    refine ⟨5468073290391805559425997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645382193594537039617331 5468073290391805559425997)
                    ·
                      refine ⟨2050527483896927084784749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468073290391805559425997 2050527483896927084784749)
                      ·
                        rfl

theorem cell23_3993388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_3993388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993388 prefixEnd_3993388 := by exact prefixLift 3993388
  have htrace : WordTrace (prefixWord ++ tailWord_3993388) baseStart_3993388 baseEnd_3993388 := by
    simpa [prefixWord, tailWord_3993388, baseEnd_3993388] using wordTrace_append hprefix tailTrace_3993388
  have hstable : (prefixWord ++ tailWord_3993388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993388).length < 2 ^ (prefixWord ++ tailWord_3993388).sum := by decide
  have hdescent : baseEnd_3993388 < baseStart_3993388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993395 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 6]
def baseStart_3993395 : Nat := 118140960795 + 3993395 * 2 ^ 59
def prefixEnd_3993395 : Nat := 4983230072969 + 3 ^ 40 * 3993395 * 2
def baseEnd_3993395 : Nat := 227836786473500950821913

theorem tailTrace_3993395 : CollatzResearch.WordTrace tailWord_3993395 prefixEnd_3993395 227836786473500950821913 := by
  unfold tailWord_3993395
  simp only [CollatzResearch.WordTrace]
  refine ⟨145651081367619407412917639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97100720911746271608611759 145651081367619407412917639)
  ·
    refine ⟨218476622051429111119376459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145651081367619407412917639 218476622051429111119376459)
    ·
      refine ⟨327714933077143666679064689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218476622051429111119376459 327714933077143666679064689)
      ·
        refine ⟨245786199807857750009298517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327714933077143666679064689 245786199807857750009298517)
        ·
          refine ⟨2880307028998333007921467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 245786199807857750009298517 2880307028998333007921467)
          ·
            refine ⟨4320460543497499511882201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880307028998333007921467 4320460543497499511882201)
            ·
              refine ⟨3240345407623124633911651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320460543497499511882201 3240345407623124633911651)
              ·
                refine ⟨4860518111434686950867477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240345407623124633911651 4860518111434686950867477)
                ·
                  refine ⟨227836786473500950821913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4860518111434686950867477 227836786473500950821913)
                  ·
                    rfl

theorem cell23_3993395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 6].length) (baseStart_3993395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993395 prefixEnd_3993395 := by exact prefixLift 3993395
  have htrace : WordTrace (prefixWord ++ tailWord_3993395) baseStart_3993395 baseEnd_3993395 := by
    simpa [prefixWord, tailWord_3993395, baseEnd_3993395] using wordTrace_append hprefix tailTrace_3993395
  have hstable : (prefixWord ++ tailWord_3993395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993395).length < 2 ^ (prefixWord ++ tailWord_3993395).sum := by decide
  have hdescent : baseEnd_3993395 < baseStart_3993395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993411 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4]
def baseStart_3993411 : Nat := 118140960795 + 3993411 * 2 ^ 59
def prefixEnd_3993411 : Nat := 4983230072969 + 3 ^ 40 * 3993411 * 2
def baseEnd_3993411 : Nat := 2050539293951980494797143

theorem tailTrace_3993411 : CollatzResearch.WordTrace tailWord_3993411 prefixEnd_3993411 2050539293951980494797143 := by
  unfold tailWord_3993411
  simp only [CollatzResearch.WordTrace]
  refine ⟨145651664935561442145500087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97101109957040961430333391 145651664935561442145500087)
  ·
    refine ⟨218477497403342163218250131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145651664935561442145500087 218477497403342163218250131)
    ·
      refine ⟨327716246105013244827375197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218477497403342163218250131 327716246105013244827375197)
      ·
        refine ⟨122893592289379966810265699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327716246105013244827375197 122893592289379966810265699)
        ·
          refine ⟨184340388434069950215398549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122893592289379966810265699 184340388434069950215398549)
          ·
            refine ⟨8640955707847028916346807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 184340388434069950215398549 8640955707847028916346807)
            ·
              refine ⟨12961433561770543374520211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8640955707847028916346807 12961433561770543374520211)
              ·
                refine ⟨19442150342655815061780317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12961433561770543374520211 19442150342655815061780317)
                ·
                  refine ⟨7290806378495930648167619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19442150342655815061780317 7290806378495930648167619)
                  ·
                    refine ⟨10936209567743895972251429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7290806378495930648167619 10936209567743895972251429)
                    ·
                      refine ⟨2050539293951980494797143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10936209567743895972251429 2050539293951980494797143)
                      ·
                        rfl

theorem cell23_3993411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_3993411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993411 prefixEnd_3993411 := by exact prefixLift 3993411
  have htrace : WordTrace (prefixWord ++ tailWord_3993411) baseStart_3993411 baseEnd_3993411 := by
    simpa [prefixWord, tailWord_3993411, baseEnd_3993411] using wordTrace_append hprefix tailTrace_3993411
  have hstable : (prefixWord ++ tailWord_3993411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993411).length < 2 ^ (prefixWord ++ tailWord_3993411).sum := by decide
  have hdescent : baseEnd_3993411 < baseStart_3993411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993479 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_3993479 : Nat := 118140960795 + 3993479 * 2 ^ 59
def prefixEnd_3993479 : Nat := 4983230072969 + 3 ^ 40 * 3993479 * 2
def baseEnd_3993479 : Nat := 2050574210636486228746831

theorem tailTrace_3993479 : CollatzResearch.WordTrace tailWord_3993479 prefixEnd_3993479 2050574210636486228746831 := by
  unfold tailWord_3993479
  simp only [CollatzResearch.WordTrace]
  refine ⟨145654145099315089758975491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97102763399543393172650327 145654145099315089758975491)
  ·
    refine ⟨218481217648972634638463237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145654145099315089758975491 218481217648972634638463237)
    ·
      refine ⟨40965228309182368994711857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218481217648972634638463237 40965228309182368994711857)
      ·
        refine ⟨30723921231886776746033893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40965228309182368994711857 30723921231886776746033893)
        ·
          refine ⟨5760735230978770639881355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30723921231886776746033893 5760735230978770639881355)
          ·
            refine ⟨8641102846468155959822033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5760735230978770639881355 8641102846468155959822033)
            ·
              refine ⟨6480827134851116969866525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8641102846468155959822033 6480827134851116969866525)
              ·
                refine ⟨2430310175569168863699947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6480827134851116969866525 2430310175569168863699947)
                ·
                  refine ⟨3645465263353753295549921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430310175569168863699947 3645465263353753295549921)
                  ·
                    refine ⟨2734098947515314971662441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645465263353753295549921 2734098947515314971662441)
                    ·
                      refine ⟨2050574210636486228746831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734098947515314971662441 2050574210636486228746831)
                      ·
                        rfl

theorem cell23_3993479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_3993479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993479 prefixEnd_3993479 := by exact prefixLift 3993479
  have htrace : WordTrace (prefixWord ++ tailWord_3993479) baseStart_3993479 baseEnd_3993479 := by
    simpa [prefixWord, tailWord_3993479, baseEnd_3993479] using wordTrace_append hprefix tailTrace_3993479
  have hstable : (prefixWord ++ tailWord_3993479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993479).length < 2 ^ (prefixWord ++ tailWord_3993479).sum := by decide
  have hdescent : baseEnd_3993479 < baseStart_3993479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993495 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3993495 : Nat := 118140960795 + 3993495 * 2 ^ 59
def prefixEnd_3993495 : Nat := 4983230072969 + 3 ^ 40 * 3993495 * 2
def baseEnd_3993495 : Nat := 2050582426326958166146757

theorem tailTrace_3993495 : CollatzResearch.WordTrace tailWord_3993495 prefixEnd_3993495 2050582426326958166146757 := by
  unfold tailWord_3993495
  simp only [CollatzResearch.WordTrace]
  refine ⟨145654728667257124491557939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97103152444838082994371959 145654728667257124491557939)
  ·
    refine ⟨218482093000885686737336909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145654728667257124491557939 218482093000885686737336909)
    ·
      refine ⟨81930784875332132526501341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218482093000885686737336909 81930784875332132526501341)
      ·
        refine ⟨30724044328249549697438003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81930784875332132526501341 30724044328249549697438003)
        ·
          refine ⟨46086066492374324546157005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30724044328249549697438003 46086066492374324546157005)
          ·
            refine ⟨17282274934640371704808877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46086066492374324546157005 17282274934640371704808877)
            ·
              refine ⟨6480853100490139389303329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17282274934640371704808877 6480853100490139389303329)
              ·
                refine ⟨4860639825367604541977497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6480853100490139389303329 4860639825367604541977497)
                ·
                  refine ⟨3645479869025703406483123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4860639825367604541977497 3645479869025703406483123)
                  ·
                    refine ⟨5468219803538555109724685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645479869025703406483123 5468219803538555109724685)
                    ·
                      refine ⟨2050582426326958166146757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468219803538555109724685 2050582426326958166146757)
                      ·
                        rfl

theorem cell23_3993495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3993495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993495 prefixEnd_3993495 := by exact prefixLift 3993495
  have htrace : WordTrace (prefixWord ++ tailWord_3993495) baseStart_3993495 baseEnd_3993495 := by
    simpa [prefixWord, tailWord_3993495, baseEnd_3993495] using wordTrace_append hprefix tailTrace_3993495
  have hstable : (prefixWord ++ tailWord_3993495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993495).length < 2 ^ (prefixWord ++ tailWord_3993495).sum := by decide
  have hdescent : baseEnd_3993495 < baseStart_3993495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993608 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3993608 : Nat := 118140960795 + 3993608 * 2 ^ 59
def prefixEnd_3993608 : Nat := 4983230072969 + 3 ^ 40 * 3993608 * 2
def baseEnd_3993608 : Nat := 2050640449640916224033737

theorem tailTrace_3993608 : CollatzResearch.WordTrace tailWord_3993608 prefixEnd_3993608 2050640449640916224033737 := by
  unfold tailWord_3993608
  simp only [CollatzResearch.WordTrace]
  refine ⟨72829425057923872395210739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97105900077231829860280985 72829425057923872395210739)
  ·
    refine ⟨109244137586885808592816109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72829425057923872395210739 109244137586885808592816109)
    ·
      refine ⟨40966551595082178222306041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109244137586885808592816109 40966551595082178222306041)
      ·
        refine ⟨30724913696311633666729531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40966551595082178222306041 30724913696311633666729531)
        ·
          refine ⟨46087370544467450500094297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30724913696311633666729531 46087370544467450500094297)
          ·
            refine ⟨34565527908350587875070723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46087370544467450500094297 34565527908350587875070723)
            ·
              refine ⟨51848291862525881812606085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34565527908350587875070723 51848291862525881812606085)
              ·
                refine ⟨9721554724223602839863641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51848291862525881812606085 9721554724223602839863641)
                ·
                  refine ⟨7291166043167702129897731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721554724223602839863641 7291166043167702129897731)
                  ·
                    refine ⟨10936749064751553194846597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291166043167702129897731 10936749064751553194846597)
                    ·
                      refine ⟨2050640449640916224033737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10936749064751553194846597 2050640449640916224033737)
                      ·
                        rfl

theorem cell23_3993608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3993608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993608 prefixEnd_3993608 := by exact prefixLift 3993608
  have htrace : WordTrace (prefixWord ++ tailWord_3993608) baseStart_3993608 baseEnd_3993608 := by
    simpa [prefixWord, tailWord_3993608, baseEnd_3993608] using wordTrace_append hprefix tailTrace_3993608
  have hstable : (prefixWord ++ tailWord_3993608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993608).length < 2 ^ (prefixWord ++ tailWord_3993608).sum := by decide
  have hdescent : baseEnd_3993608 < baseStart_3993608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993611 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_3993611 : Nat := 118140960795 + 3993611 * 2 ^ 59
def prefixEnd_3993611 : Nat := 4983230072969 + 3 ^ 40 * 3993611 * 2
def baseEnd_3993611 : Nat := 2050641990082879712296223

theorem tailTrace_3993611 : CollatzResearch.WordTrace tailWord_3993611 prefixEnd_3993611 2050641990082879712296223 := by
  unfold tailWord_3993611
  simp only [CollatzResearch.WordTrace]
  refine ⟨145658959534836876302780687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97105973023224584201853791 145658959534836876302780687)
  ·
    refine ⟨218488439302255314454171031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145658959534836876302780687 218488439302255314454171031)
    ·
      refine ⟨327732658953382971681256547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218488439302255314454171031 327732658953382971681256547)
      ·
        refine ⟨491598988430074457521884821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327732658953382971681256547 491598988430074457521884821)
        ·
          refine ⟨23043702582659740196338351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 491598988430074457521884821 23043702582659740196338351)
          ·
            refine ⟨34565553873989610294507527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23043702582659740196338351 34565553873989610294507527)
            ·
              refine ⟨51848330810984415441761291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34565553873989610294507527 51848330810984415441761291)
              ·
                refine ⟨77772496216476623162641937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51848330810984415441761291 77772496216476623162641937)
                ·
                  refine ⟨58329372162357467371981453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77772496216476623162641937 58329372162357467371981453)
                  ·
                    refine ⟨21873514560884050264493045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58329372162357467371981453 21873514560884050264493045)
                    ·
                      refine ⟨2050641990082879712296223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21873514560884050264493045 2050641990082879712296223)
                      ·
                        rfl

theorem cell23_3993611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_3993611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993611 prefixEnd_3993611 := by exact prefixLift 3993611
  have htrace : WordTrace (prefixWord ++ tailWord_3993611) baseStart_3993611 baseEnd_3993611 := by
    simpa [prefixWord, tailWord_3993611, baseEnd_3993611] using wordTrace_append hprefix tailTrace_3993611
  have hstable : (prefixWord ++ tailWord_3993611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993611).length < 2 ^ (prefixWord ++ tailWord_3993611).sum := by decide
  have hdescent : baseEnd_3993611 < baseStart_3993611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993639 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3993639 : Nat := 118140960795 + 3993639 * 2 ^ 59
def prefixEnd_3993639 : Nat := 4983230072969 + 3 ^ 40 * 3993639 * 2
def baseEnd_3993639 : Nat := 683552122513735200915365

theorem tailTrace_3993639 : CollatzResearch.WordTrace tailWord_3993639 prefixEnd_3993639 683552122513735200915365 := by
  unfold tailWord_3993639
  simp only [CollatzResearch.WordTrace]
  refine ⟨145659980778735437084799971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97106653852490291389866647 145659980778735437084799971)
  ·
    refine ⟨218489971168103155627199957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145659980778735437084799971 218489971168103155627199957)
    ·
      refine ⟨5120858699252417710012499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 218489971168103155627199957 5120858699252417710012499)
      ·
        refine ⟨7681288048878626565018749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5120858699252417710012499 7681288048878626565018749)
        ·
          refine ⟨2880483018329484961882031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7681288048878626565018749 2880483018329484961882031)
          ·
            refine ⟨4320724527494227442823047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880483018329484961882031 4320724527494227442823047)
            ·
              refine ⟨6481086791241341164234571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320724527494227442823047 6481086791241341164234571)
              ·
                refine ⟨9721630186862011746351857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481086791241341164234571 9721630186862011746351857)
                ·
                  refine ⟨7291222640146508809763893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721630186862011746351857 7291222640146508809763893)
                  ·
                    refine ⟨683552122513735200915365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7291222640146508809763893 683552122513735200915365)
                    ·
                      rfl

theorem cell23_3993639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3993639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993639 prefixEnd_3993639 := by exact prefixLift 3993639
  have htrace : WordTrace (prefixWord ++ tailWord_3993639) baseStart_3993639 baseEnd_3993639 := by
    simpa [prefixWord, tailWord_3993639, baseEnd_3993639] using wordTrace_append hprefix tailTrace_3993639
  have hstable : (prefixWord ++ tailWord_3993639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993639).length < 2 ^ (prefixWord ++ tailWord_3993639).sum := by decide
  have hdescent : baseEnd_3993639 < baseStart_3993639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993642 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3993642 : Nat := 118140960795 + 3993642 * 2 ^ 59
def prefixEnd_3993642 : Nat := 4983230072969 + 3 ^ 40 * 3993642 * 2
def baseEnd_3993642 : Nat := 2050657907983169091008581

theorem tailTrace_3993642 : CollatzResearch.WordTrace tailWord_3993642 prefixEnd_3993642 2050657907983169091008581 := by
  unfold tailWord_3993642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415022549431142149289795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97106726798483045731439453 36415022549431142149289795)
  ·
    refine ⟨54622533824146713223934693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36415022549431142149289795 54622533824146713223934693)
    ·
      refine ⟨10241725092027508729487755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54622533824146713223934693 10241725092027508729487755)
      ·
        refine ⟨15362587638041263094231633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241725092027508729487755 15362587638041263094231633)
        ·
          refine ⟨11521940728530947320673725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15362587638041263094231633 11521940728530947320673725)
          ·
            refine ⟨4320727773199105245252647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11521940728530947320673725 4320727773199105245252647)
            ·
              refine ⟨6481091659798657867878971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320727773199105245252647 6481091659798657867878971)
              ·
                refine ⟨9721637489697986801818457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6481091659798657867878971 9721637489697986801818457)
                ·
                  refine ⟨7291228117273490101363843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9721637489697986801818457 7291228117273490101363843)
                  ·
                    refine ⟨10936842175910235152045765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7291228117273490101363843 10936842175910235152045765)
                    ·
                      refine ⟨2050657907983169091008581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10936842175910235152045765 2050657907983169091008581)
                      ·
                        rfl

theorem cell23_3993642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3993642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993642 prefixEnd_3993642 := by exact prefixLift 3993642
  have htrace : WordTrace (prefixWord ++ tailWord_3993642) baseStart_3993642 baseEnd_3993642 := by
    simpa [prefixWord, tailWord_3993642, baseEnd_3993642] using wordTrace_append hprefix tailTrace_3993642
  have hstable : (prefixWord ++ tailWord_3993642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993642).length < 2 ^ (prefixWord ++ tailWord_3993642).sum := by decide
  have hdescent : baseEnd_3993642 < baseStart_3993642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993665 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 6]
def baseStart_3993665 : Nat := 118140960795 + 3993665 * 2 ^ 59
def prefixEnd_3993665 : Nat := 4983230072969 + 3 ^ 40 * 3993665 * 2
def baseEnd_3993665 : Nat := 227852190893135833446775

theorem tailTrace_3993665 : CollatzResearch.WordTrace tailWord_3993665 prefixEnd_3993665 227852190893135833446775 := by
  unfold tailWord_3993665
  simp only [CollatzResearch.WordTrace]
  refine ⟨145660929076641243525246449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97107286051094162350164299 145660929076641243525246449)
  ·
    refine ⟨109245696807480932643934837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145660929076641243525246449 109245696807480932643934837)
    ·
      refine ⟨10241784075701337435368891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109245696807480932643934837 10241784075701337435368891)
      ·
        refine ⟨15362676113552006153053337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241784075701337435368891 15362676113552006153053337)
        ·
          refine ⟨11522007085164004614790003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15362676113552006153053337 11522007085164004614790003)
          ·
            refine ⟨17283010627746006922185005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11522007085164004614790003 17283010627746006922185005)
            ·
              refine ⟨6481128985404752595819377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17283010627746006922185005 6481128985404752595819377)
              ·
                refine ⟨4860846739053564446864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6481128985404752595819377 4860846739053564446864533)
                ·
                  refine ⟨227852190893135833446775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4860846739053564446864533 227852190893135833446775)
                  ·
                    rfl

theorem cell23_3993665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_3993665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993665 prefixEnd_3993665 := by exact prefixLift 3993665
  have htrace : WordTrace (prefixWord ++ tailWord_3993665) baseStart_3993665 baseEnd_3993665 := by
    simpa [prefixWord, tailWord_3993665, baseEnd_3993665] using wordTrace_append hprefix tailTrace_3993665
  have hstable : (prefixWord ++ tailWord_3993665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993665).length < 2 ^ (prefixWord ++ tailWord_3993665).sum := by decide
  have hdescent : baseEnd_3993665 < baseStart_3993665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993682 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_3993682 : Nat := 118140960795 + 3993682 * 2 ^ 59
def prefixEnd_3993682 : Nat := 4983230072969 + 3 ^ 40 * 3993682 * 2
def baseEnd_3993682 : Nat := 227853160801038770500933

theorem tailTrace_3993682 : CollatzResearch.WordTrace tailWord_3993682 prefixEnd_3993682 227853160801038770500933 := by
  unfold tailWord_3993682
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415387279394913857153825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97107699411719770285743533 36415387279394913857153825)
  ·
    refine ⟨27311540459546185392865369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36415387279394913857153825 27311540459546185392865369)
    ·
      refine ⟨20483655344659639044649027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27311540459546185392865369 20483655344659639044649027)
      ·
        refine ⟨30725483016989458566973541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20483655344659639044649027 30725483016989458566973541)
        ·
          refine ⟨5761028065685523481307539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30725483016989458566973541 5761028065685523481307539)
          ·
            refine ⟨8641542098528285221961309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761028065685523481307539 8641542098528285221961309)
            ·
              refine ⟨3240578286948106958235491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8641542098528285221961309 3240578286948106958235491)
              ·
                refine ⟨4860867430422160437353237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240578286948106958235491 4860867430422160437353237)
                ·
                  refine ⟨227853160801038770500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4860867430422160437353237 227853160801038770500933)
                  ·
                    rfl

theorem cell23_3993682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_3993682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993682 prefixEnd_3993682 := by exact prefixLift 3993682
  have htrace : WordTrace (prefixWord ++ tailWord_3993682) baseStart_3993682 baseEnd_3993682 := by
    simpa [prefixWord, tailWord_3993682, baseEnd_3993682] using wordTrace_append hprefix tailTrace_3993682
  have hstable : (prefixWord ++ tailWord_3993682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993682).length < 2 ^ (prefixWord ++ tailWord_3993682).sum := by decide
  have hdescent : baseEnd_3993682 < baseStart_3993682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993685 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3993685 : Nat := 118140960795 + 3993685 * 2 ^ 59
def prefixEnd_3993685 : Nat := 4983230072969 + 3 ^ 40 * 3993685 * 2
def baseEnd_3993685 : Nat := 2050679987651312422770883

theorem tailTrace_3993685 : CollatzResearch.WordTrace tailWord_3993685 prefixEnd_3993685 2050679987651312422770883 := by
  unfold tailWord_3993685
  simp only [CollatzResearch.WordTrace]
  refine ⟨145661658536568786940974509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97107772357712524627316339 145661658536568786940974509)
  ·
    refine ⟨54623121951213295102865441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145661658536568786940974509 54623121951213295102865441)
    ·
      refine ⟨40967341463409971327149081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54623121951213295102865441 40967341463409971327149081)
      ·
        refine ⟨30725506097557478495361811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40967341463409971327149081 30725506097557478495361811)
        ·
          refine ⟨46088259146336217743042717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30725506097557478495361811 46088259146336217743042717)
          ·
            refine ⟨17283097179876081653641019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46088259146336217743042717 17283097179876081653641019)
            ·
              refine ⟨25924645769814122480461529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17283097179876081653641019 25924645769814122480461529)
              ·
                refine ⟨19443484327360591860346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25924645769814122480461529 19443484327360591860346147)
                ·
                  refine ⟨29165226491040887790519221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19443484327360591860346147 29165226491040887790519221)
                  ·
                    refine ⟨2734239983535083230361177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29165226491040887790519221 2734239983535083230361177)
                    ·
                      refine ⟨2050679987651312422770883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734239983535083230361177 2050679987651312422770883)
                      ·
                        rfl

theorem cell23_3993685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3993685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993685 prefixEnd_3993685 := by exact prefixLift 3993685
  have htrace : WordTrace (prefixWord ++ tailWord_3993685) baseStart_3993685 baseEnd_3993685 := by
    simpa [prefixWord, tailWord_3993685, baseEnd_3993685] using wordTrace_append hprefix tailTrace_3993685
  have hstable : (prefixWord ++ tailWord_3993685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993685).length < 2 ^ (prefixWord ++ tailWord_3993685).sum := by decide
  have hdescent : baseEnd_3993685 < baseStart_3993685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993692 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3993692 : Nat := 118140960795 + 3993692 * 2 ^ 59
def prefixEnd_3993692 : Nat := 4983230072969 + 3 ^ 40 * 3993692 * 2
def baseEnd_3993692 : Nat := 2050683582015893895383351

theorem tailTrace_3993692 : CollatzResearch.WordTrace tailWord_3993692 prefixEnd_3993692 2050683582015893895383351 := by
  unfold tailWord_3993692
  simp only [CollatzResearch.WordTrace]
  refine ⟨72830956923771713568239665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97107942565028951424319553 72830956923771713568239665)
  ·
    refine ⟨54623217692828785176179749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72830956923771713568239665 54623217692828785176179749)
    ·
      refine ⟨10241853317405397220533703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54623217692828785176179749 10241853317405397220533703)
      ·
        refine ⟨15362779976108095830800555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10241853317405397220533703 15362779976108095830800555)
        ·
          refine ⟨23044169964162143746200833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15362779976108095830800555 23044169964162143746200833)
          ·
            refine ⟨17283127473121607809650625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23044169964162143746200833 17283127473121607809650625)
            ·
              refine ⟨12962345604841205857237969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17283127473121607809650625 12962345604841205857237969)
              ·
                refine ⟨9721759203630904392928477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12962345604841205857237969 9721759203630904392928477)
                ·
                  refine ⟨3645659701361589147348179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9721759203630904392928477 3645659701361589147348179)
                  ·
                    refine ⟨5468489552042383721022269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645659701361589147348179 5468489552042383721022269)
                    ·
                      refine ⟨2050683582015893895383351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468489552042383721022269 2050683582015893895383351)
                      ·
                        rfl

theorem cell23_3993692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3993692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993692 prefixEnd_3993692 := by exact prefixLift 3993692
  have htrace : WordTrace (prefixWord ++ tailWord_3993692) baseStart_3993692 baseEnd_3993692 := by
    simpa [prefixWord, tailWord_3993692, baseEnd_3993692] using wordTrace_append hprefix tailTrace_3993692
  have hstable : (prefixWord ++ tailWord_3993692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993692).length < 2 ^ (prefixWord ++ tailWord_3993692).sum := by decide
  have hdescent : baseEnd_3993692 < baseStart_3993692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993725 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3993725 : Nat := 118140960795 + 3993725 * 2 ^ 59
def prefixEnd_3993725 : Nat := 4983230072969 + 3 ^ 40 * 3993725 * 2
def baseEnd_3993725 : Nat := 683566842292497422090233

theorem tailTrace_3993725 : CollatzResearch.WordTrace tailWord_3993725 prefixEnd_3993725 683566842292497422090233 := by
  unfold tailWord_3993725
  simp only [CollatzResearch.WordTrace]
  refine ⟨145663117456423873772430629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97108744970949249181620419 145663117456423873772430629)
  ·
    refine ⟨27311834523079476332330743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145663117456423873772430629 27311834523079476332330743)
    ·
      refine ⟨40967751784619214498496115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27311834523079476332330743 40967751784619214498496115)
      ·
        refine ⟨61451627676928821747744173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40967751784619214498496115 61451627676928821747744173)
        ·
          refine ⟨23044360378848308155404065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61451627676928821747744173 23044360378848308155404065)
          ·
            refine ⟨17283270284136231116553049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23044360378848308155404065 17283270284136231116553049)
            ·
              refine ⟨12962452713102173337414787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17283270284136231116553049 12962452713102173337414787)
              ·
                refine ⟨19443679069653260006122181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962452713102173337414787 19443679069653260006122181)
                ·
                  refine ⟨3645689825559986251147909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19443679069653260006122181 3645689825559986251147909)
                  ·
                    refine ⟨683566842292497422090233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3645689825559986251147909 683566842292497422090233)
                    ·
                      rfl

theorem cell23_3993725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3993725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993725 prefixEnd_3993725 := by exact prefixLift 3993725
  have htrace : WordTrace (prefixWord ++ tailWord_3993725) baseStart_3993725 baseEnd_3993725 := by
    simpa [prefixWord, tailWord_3993725, baseEnd_3993725] using wordTrace_append hprefix tailTrace_3993725
  have hstable : (prefixWord ++ tailWord_3993725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993725).length < 2 ^ (prefixWord ++ tailWord_3993725).sum := by decide
  have hdescent : baseEnd_3993725 < baseStart_3993725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993738 : List Nat := [3, 1, 2, 3, 1, 2, 1, 10]
def baseStart_3993738 : Nat := 118140960795 + 3993738 * 2 ^ 59
def prefixEnd_3993738 : Nat := 4983230072969 + 3 ^ 40 * 3993738 * 2
def baseEnd_3993738 : Nat := 75952118597259285755857

theorem tailTrace_3993738 : CollatzResearch.WordTrace tailWord_3993738 prefixEnd_3993738 75952118597259285755857 := by
  unfold tailWord_3993738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36415897901344194248163467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97109061070251184661769245 36415897901344194248163467)
  ·
    refine ⟨54623846852016291372245201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36415897901344194248163467 54623846852016291372245201)
    ·
      refine ⟨40967885139012218529183901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54623846852016291372245201 40967885139012218529183901)
      ·
        refine ⟨15362956927129581948443963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40967885139012218529183901 15362956927129581948443963)
        ·
          refine ⟨23044435390694372922665945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15362956927129581948443963 23044435390694372922665945)
          ·
            refine ⟨17283326543020779691999459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23044435390694372922665945 17283326543020779691999459)
            ·
              refine ⟨25924989814531169537999189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17283326543020779691999459 25924989814531169537999189)
              ·
                refine ⟨75952118597259285755857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25924989814531169537999189 75952118597259285755857)
                ·
                  rfl

theorem cell23_3993738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_3993738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993738 prefixEnd_3993738 := by exact prefixLift 3993738
  have htrace : WordTrace (prefixWord ++ tailWord_3993738) baseStart_3993738 baseEnd_3993738 := by
    simpa [prefixWord, tailWord_3993738, baseEnd_3993738] using wordTrace_append hprefix tailTrace_3993738
  have hstable : (prefixWord ++ tailWord_3993738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993738).length < 2 ^ (prefixWord ++ tailWord_3993738).sum := by decide
  have hdescent : baseEnd_3993738 < baseStart_3993738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993752 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3993752 : Nat := 118140960795 + 3993752 * 2 ^ 59
def prefixEnd_3993752 : Nat := 4983230072969 + 3 ^ 40 * 3993752 * 2
def baseEnd_3993752 : Nat := 2050714390855163660633075

theorem tailTrace_3993752 : CollatzResearch.WordTrace tailWord_3993752 prefixEnd_3993752 2050714390855163660633075 := by
  unfold tailWord_3993752
  simp only [CollatzResearch.WordTrace]
  refine ⟨72832051113663028691831755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97109401484884038255775673 72832051113663028691831755)
  ·
    refine ⟨109248076670494543037747633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72832051113663028691831755 109248076670494543037747633)
    ·
      refine ⟨81936057502870907278310725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109248076670494543037747633 81936057502870907278310725)
      ·
        refine ⟨15363010781788295114683261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81936057502870907278310725 15363010781788295114683261)
        ·
          refine ⟨5761129043170610668006223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15363010781788295114683261 5761129043170610668006223)
          ·
            refine ⟨8641693564755916002009335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761129043170610668006223 8641693564755916002009335)
            ·
              refine ⟨12962540347133874003014003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641693564755916002009335 12962540347133874003014003)
              ·
                refine ⟨19443810520700811004521005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962540347133874003014003 19443810520700811004521005)
                ·
                  refine ⟨7291428945262804126695377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19443810520700811004521005 7291428945262804126695377)
                  ·
                    refine ⟨5468571708947103095021533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291428945262804126695377 5468571708947103095021533)
                    ·
                      refine ⟨2050714390855163660633075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468571708947103095021533 2050714390855163660633075)
                      ·
                        rfl

theorem cell23_3993752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3993752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993752 prefixEnd_3993752 := by exact prefixLift 3993752
  have htrace : WordTrace (prefixWord ++ tailWord_3993752) baseStart_3993752 baseEnd_3993752 := by
    simpa [prefixWord, tailWord_3993752, baseEnd_3993752] using wordTrace_append hprefix tailTrace_3993752
  have hstable : (prefixWord ++ tailWord_3993752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993752).length < 2 ^ (prefixWord ++ tailWord_3993752).sum := by decide
  have hdescent : baseEnd_3993752 < baseStart_3993752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993762 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3993762 : Nat := 118140960795 + 3993762 * 2 ^ 59
def prefixEnd_3993762 : Nat := 4983230072969 + 3 ^ 40 * 3993762 * 2
def baseEnd_3993762 : Nat := 2050719525661708621508029

theorem tailTrace_3993762 : CollatzResearch.WordTrace tailWord_3993762 prefixEnd_3993762 2050719525661708621508029 := by
  unfold tailWord_3993762
  simp only [CollatzResearch.WordTrace]
  refine ⟨36416116739322457272881885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97109644638193219394351693 36416116739322457272881885)
  ·
    refine ⟨13656043777245921477330707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36416116739322457272881885 13656043777245921477330707)
    ·
      refine ⟨20484065665868882215996061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13656043777245921477330707 20484065665868882215996061)
      ·
        refine ⟨7681524624700830830998523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20484065665868882215996061 7681524624700830830998523)
        ·
          refine ⟨11522286937051246246497785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7681524624700830830998523 11522286937051246246497785)
          ·
            refine ⟨8641715202788434684873339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11522286937051246246497785 8641715202788434684873339)
            ·
              refine ⟨12962572804182652027310009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641715202788434684873339 12962572804182652027310009)
              ·
                refine ⟨9721929603136989020482507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12962572804182652027310009 9721929603136989020482507)
                ·
                  refine ⟨14582894404705483530723761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721929603136989020482507 14582894404705483530723761)
                  ·
                    refine ⟨10937170803529112648042821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14582894404705483530723761 10937170803529112648042821)
                    ·
                      refine ⟨2050719525661708621508029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10937170803529112648042821 2050719525661708621508029)
                      ·
                        rfl

theorem cell23_3993762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3993762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993762 prefixEnd_3993762 := by exact prefixLift 3993762
  have htrace : WordTrace (prefixWord ++ tailWord_3993762) baseStart_3993762 baseEnd_3993762 := by
    simpa [prefixWord, tailWord_3993762, baseEnd_3993762] using wordTrace_append hprefix tailTrace_3993762
  have hstable : (prefixWord ++ tailWord_3993762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993762).length < 2 ^ (prefixWord ++ tailWord_3993762).sum := by decide
  have hdescent : baseEnd_3993762 < baseStart_3993762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993765 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_3993765 : Nat := 118140960795 + 3993765 * 2 ^ 59
def prefixEnd_3993765 : Nat := 4983230072969 + 3 ^ 40 * 3993765 * 2
def baseEnd_3993765 : Nat := 2050721066103672109770515

theorem tailTrace_3993765 : CollatzResearch.WordTrace tailWord_3993765 prefixEnd_3993765 2050721066103672109770515 := by
  unfold tailWord_3993765
  simp only [CollatzResearch.WordTrace]
  refine ⟨145664576376278960603886749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97109717584185973735924499 145664576376278960603886749)
  ·
    refine ⟨54624216141104610226457531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145664576376278960603886749 54624216141104610226457531)
    ·
      refine ⟨81936324211656915339686297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54624216141104610226457531 81936324211656915339686297)
      ·
        refine ⟨61452243158742686504764723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81936324211656915339686297 61452243158742686504764723)
        ·
          refine ⟨92178364738114029757147085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61452243158742686504764723 92178364738114029757147085)
          ·
            refine ⟨34566886776792761158930157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92178364738114029757147085 34566886776792761158930157)
            ·
              refine ⟨12962582541297285434598809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34566886776792761158930157 12962582541297285434598809)
              ·
                refine ⟨9721936905972964075949107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12962582541297285434598809 9721936905972964075949107)
                ·
                  refine ⟨14582905358959446113923661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9721936905972964075949107 14582905358959446113923661)
                  ·
                    refine ⟨5468589509609792292721373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14582905358959446113923661 5468589509609792292721373)
                    ·
                      refine ⟨2050721066103672109770515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468589509609792292721373 2050721066103672109770515)
                      ·
                        rfl

theorem cell23_3993765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_3993765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993765 prefixEnd_3993765 := by exact prefixLift 3993765
  have htrace : WordTrace (prefixWord ++ tailWord_3993765) baseStart_3993765 baseEnd_3993765 := by
    simpa [prefixWord, tailWord_3993765, baseEnd_3993765] using wordTrace_append hprefix tailTrace_3993765
  have hstable : (prefixWord ++ tailWord_3993765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993765).length < 2 ^ (prefixWord ++ tailWord_3993765).sum := by decide
  have hdescent : baseEnd_3993765 < baseStart_3993765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993783 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 1, 2, 2]
def baseStart_3993783 : Nat := 118140960795 + 3993783 * 2 ^ 59
def prefixEnd_3993783 : Nat := 4983230072969 + 3 ^ 40 * 3993783 * 2
def baseEnd_3993783 : Nat := 2050730308755453039345433

theorem tailTrace_3993783 : CollatzResearch.WordTrace tailWord_3993783 prefixEnd_3993783 2050730308755453039345433 := by
  unfold tailWord_3993783
  simp only [CollatzResearch.WordTrace]
  refine ⟨145665232890213749678042003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97110155260142499785361335 145665232890213749678042003)
  ·
    refine ⟨218497849335320624517063005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145665232890213749678042003 218497849335320624517063005)
    ·
      refine ⟨81936693500745234193898627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218497849335320624517063005 81936693500745234193898627)
      ·
        refine ⟨122905040251117851290847941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81936693500745234193898627 122905040251117851290847941)
        ·
          refine ⟨23044695047084597117033989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122905040251117851290847941 23044695047084597117033989)
          ·
            refine ⟨4320880321328361959443873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23044695047084597117033989 4320880321328361959443873)
            ·
              refine ⟨3240660240996271469582905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320880321328361959443873 3240660240996271469582905)
              ·
                refine ⟨2430495180747203602187179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240660240996271469582905 2430495180747203602187179)
                ·
                  refine ⟨3645742771120805403280769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430495180747203602187179 3645742771120805403280769)
                  ·
                    refine ⟨2734307078340604052460577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645742771120805403280769 2734307078340604052460577)
                    ·
                      refine ⟨2050730308755453039345433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734307078340604052460577 2050730308755453039345433)
                      ·
                        rfl

theorem cell23_3993783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_3993783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993783 prefixEnd_3993783 := by exact prefixLift 3993783
  have htrace : WordTrace (prefixWord ++ tailWord_3993783) baseStart_3993783 baseEnd_3993783 := by
    simpa [prefixWord, tailWord_3993783, baseEnd_3993783] using wordTrace_append hprefix tailTrace_3993783
  have hstable : (prefixWord ++ tailWord_3993783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993783).length < 2 ^ (prefixWord ++ tailWord_3993783).sum := by decide
  have hdescent : baseEnd_3993783 < baseStart_3993783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993792 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2]
def baseStart_3993792 : Nat := 118140960795 + 3993792 * 2 ^ 59
def prefixEnd_3993792 : Nat := 4983230072969 + 3 ^ 40 * 3993792 * 2
def baseEnd_3993792 : Nat := 2050734930081343504132891

theorem tailTrace_3993792 : CollatzResearch.WordTrace tailWord_3993792 prefixEnd_3993792 2050734930081343504132891 := by
  unfold tailWord_3993792
  simp only [CollatzResearch.WordTrace]
  refine ⟨72832780573590572107559815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97110374098120762810079753 72832780573590572107559815)
  ·
    refine ⟨109249170860385858161339723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72832780573590572107559815 109249170860385858161339723)
    ·
      refine ⟨163873756290578787242009585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109249170860385858161339723 163873756290578787242009585)
      ·
        refine ⟨122905317217934090431507189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163873756290578787242009585 122905317217934090431507189)
        ·
          refine ⟨11522373489181320977953799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122905317217934090431507189 11522373489181320977953799)
          ·
            refine ⟨17283560233771981466930699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11522373489181320977953799 17283560233771981466930699)
            ·
              refine ⟨25925340350657972200396049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17283560233771981466930699 25925340350657972200396049)
              ·
                refine ⟨19444005262993479150297037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25925340350657972200396049 19444005262993479150297037)
                ·
                  refine ⟨7291501973622554681361389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19444005262993479150297037 7291501973622554681361389)
                  ·
                    refine ⟨2734313240108458005510521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7291501973622554681361389 2734313240108458005510521)
                    ·
                      refine ⟨2050734930081343504132891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734313240108458005510521 2050734930081343504132891)
                      ·
                        rfl

theorem cell23_3993792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_3993792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993792 prefixEnd_3993792 := by exact prefixLift 3993792
  have htrace : WordTrace (prefixWord ++ tailWord_3993792) baseStart_3993792 baseEnd_3993792 := by
    simpa [prefixWord, tailWord_3993792, baseEnd_3993792] using wordTrace_append hprefix tailTrace_3993792
  have hstable : (prefixWord ++ tailWord_3993792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993792).length < 2 ^ (prefixWord ++ tailWord_3993792).sum := by decide
  have hdescent : baseEnd_3993792 < baseStart_3993792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993820 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3993820 : Nat := 118140960795 + 3993820 * 2 ^ 59
def prefixEnd_3993820 : Nat := 4983230072969 + 3 ^ 40 * 3993820 * 2
def baseEnd_3993820 : Nat := 2050749307539669394582763

theorem tailTrace_3993820 : CollatzResearch.WordTrace tailWord_3993820 prefixEnd_3993820 2050749307539669394582763 := by
  unfold tailWord_3993820
  simp only [CollatzResearch.WordTrace]
  refine ⟨72833291195539852498569457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97111054927386469998092609 72833291195539852498569457)
  ·
    refine ⟨54624968396654889373927093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72833291195539852498569457 54624968396654889373927093)
    ·
      refine ⟨5121090787186395878805665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54624968396654889373927093 5121090787186395878805665)
      ·
        refine ⟨3840818090389796909104249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5121090787186395878805665 3840818090389796909104249)
        ·
          refine ⟨2880613567792347681828187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840818090389796909104249 2880613567792347681828187)
          ·
            refine ⟨4320920351688521522742281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2880613567792347681828187 4320920351688521522742281)
            ·
              refine ⟨3240690263766391142056711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4320920351688521522742281 3240690263766391142056711)
              ·
                refine ⟨4861035395649586713085067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240690263766391142056711 4861035395649586713085067)
                ·
                  refine ⟨7291553093474380069627601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861035395649586713085067 7291553093474380069627601)
                  ·
                    refine ⟨5468664820105785052220701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291553093474380069627601 5468664820105785052220701)
                    ·
                      refine ⟨2050749307539669394582763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468664820105785052220701 2050749307539669394582763)
                      ·
                        rfl

theorem cell23_3993820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3993820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993820 prefixEnd_3993820 := by exact prefixLift 3993820
  have htrace : WordTrace (prefixWord ++ tailWord_3993820) baseStart_3993820 baseEnd_3993820 := by
    simpa [prefixWord, tailWord_3993820, baseEnd_3993820] using wordTrace_append hprefix tailTrace_3993820
  have hstable : (prefixWord ++ tailWord_3993820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993820).length < 2 ^ (prefixWord ++ tailWord_3993820).sum := by decide
  have hdescent : baseEnd_3993820 < baseStart_3993820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993828 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 11]
def baseStart_3993828 : Nat := 118140960795 + 3993828 * 2 ^ 59
def prefixEnd_3993828 : Nat := 4983230072969 + 3 ^ 40 * 3993828 * 2
def baseEnd_3993828 : Nat := 227861490598322818142525

theorem tailTrace_3993828 : CollatzResearch.WordTrace tailWord_3993828 prefixEnd_3993828 227861490598322818142525 := by
  unfold tailWord_3993828
  simp only [CollatzResearch.WordTrace]
  refine ⟨72833437087525361181715069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97111249450033814908953425 72833437087525361181715069)
  ·
    refine ⟨27312538907822010443143151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72833437087525361181715069 27312538907822010443143151)
    ·
      refine ⟨40968808361733015664714727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27312538907822010443143151 40968808361733015664714727)
      ·
        refine ⟨61453212542599523497072091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40968808361733015664714727 61453212542599523497072091)
        ·
          refine ⟨92179818813899285245608137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61453212542599523497072091 92179818813899285245608137)
          ·
            refine ⟨69134864110424463934206103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92179818813899285245608137 69134864110424463934206103)
            ·
              refine ⟨103702296165636695901309155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69134864110424463934206103 103702296165636695901309155)
              ·
                refine ⟨155553444248455043851963733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103702296165636695901309155 155553444248455043851963733)
                ·
                  refine ⟨227861490598322818142525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 155553444248455043851963733 227861490598322818142525)
                  ·
                    rfl

theorem cell23_3993828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_3993828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993828 prefixEnd_3993828 := by exact prefixLift 3993828
  have htrace : WordTrace (prefixWord ++ tailWord_3993828) baseStart_3993828 baseEnd_3993828 := by
    simpa [prefixWord, tailWord_3993828, baseEnd_3993828] using wordTrace_append hprefix tailTrace_3993828
  have hstable : (prefixWord ++ tailWord_3993828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993828).length < 2 ^ (prefixWord ++ tailWord_3993828).sum := by decide
  have hdescent : baseEnd_3993828 < baseStart_3993828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993839 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 4, 2, 2]
def baseStart_3993839 : Nat := 118140960795 + 3993839 * 2 ^ 59
def prefixEnd_3993839 : Nat := 4983230072969 + 3 ^ 40 * 3993839 * 2
def baseEnd_3993839 : Nat := 2050759063672104820245175

theorem tailTrace_3993839 : CollatzResearch.WordTrace tailWord_3993839 prefixEnd_3993839 2050759063672104820245175 := by
  unfold tailWord_3993839
  simp only [CollatzResearch.WordTrace]
  refine ⟨145667275378010871242080571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97111516918673914161387047 145667275378010871242080571)
  ·
    refine ⟨218500913067016306863120857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145667275378010871242080571 218500913067016306863120857)
    ·
      refine ⟨163875684800262230147340643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218500913067016306863120857 163875684800262230147340643)
      ·
        refine ⟨245813527200393345221010965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163875684800262230147340643 245813527200393345221010965)
        ·
          refine ⟨11522509087518438057234889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 245813527200393345221010965 11522509087518438057234889)
          ·
            refine ⟨8641881815638828542926167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11522509087518438057234889 8641881815638828542926167)
            ·
              refine ⟨12962822723458242814389251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641881815638828542926167 12962822723458242814389251)
              ·
                refine ⟨19444234085187364221583877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12962822723458242814389251 19444234085187364221583877)
                ·
                  refine ⟨3645793890972630791546977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19444234085187364221583877 3645793890972630791546977)
                  ·
                    refine ⟨2734345418229473093660233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3645793890972630791546977 2734345418229473093660233)
                    ·
                      refine ⟨2050759063672104820245175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734345418229473093660233 2050759063672104820245175)
                      ·
                        rfl

theorem cell23_3993839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 2, 2].length) (baseStart_3993839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993839 prefixEnd_3993839 := by exact prefixLift 3993839
  have htrace : WordTrace (prefixWord ++ tailWord_3993839) baseStart_3993839 baseEnd_3993839 := by
    simpa [prefixWord, tailWord_3993839, baseEnd_3993839] using wordTrace_append hprefix tailTrace_3993839
  have hstable : (prefixWord ++ tailWord_3993839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993839).length < 2 ^ (prefixWord ++ tailWord_3993839).sum := by decide
  have hdescent : baseEnd_3993839 < baseStart_3993839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993855 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_3993855 : Nat := 118140960795 + 3993855 * 2 ^ 59
def prefixEnd_3993855 : Nat := 4983230072969 + 3 ^ 40 * 3993855 * 2
def baseEnd_3993855 : Nat := 2050767279362576757645101

theorem tailTrace_3993855 : CollatzResearch.WordTrace tailWord_3993855 prefixEnd_3993855 2050767279362576757645101 := by
  unfold tailWord_3993855
  simp only [CollatzResearch.WordTrace]
  refine ⟨145667858945952905974663019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97111905963968603983108679 145667858945952905974663019)
  ·
    refine ⟨218501788418929358961994529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145667858945952905974663019 218501788418929358961994529)
    ·
      refine ⟨163876341314197019221495897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218501788418929358961994529 163876341314197019221495897)
      ·
        refine ⟨122907255985647764416121923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163876341314197019221495897 122907255985647764416121923)
        ·
          refine ⟨184360883978471646624182885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122907255985647764416121923 184360883978471646624182885)
          ·
            refine ⟨34567665745963433742034291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184360883978471646624182885 34567665745963433742034291)
            ·
              refine ⟨51851498618945150613051437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34567665745963433742034291 51851498618945150613051437)
              ·
                refine ⟨19444311982104431479894289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51851498618945150613051437 19444311982104431479894289)
                ·
                  refine ⟨14583233986578323609920717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19444311982104431479894289 14583233986578323609920717)
                  ·
                    refine ⟨5468712744966871353720269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14583233986578323609920717 5468712744966871353720269)
                    ·
                      refine ⟨2050767279362576757645101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468712744966871353720269 2050767279362576757645101)
                      ·
                        rfl

theorem cell23_3993855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_3993855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993855 prefixEnd_3993855 := by exact prefixLift 3993855
  have htrace : WordTrace (prefixWord ++ tailWord_3993855) baseStart_3993855 baseEnd_3993855 := by
    simpa [prefixWord, tailWord_3993855, baseEnd_3993855] using wordTrace_append hprefix tailTrace_3993855
  have hstable : (prefixWord ++ tailWord_3993855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993855).length < 2 ^ (prefixWord ++ tailWord_3993855).sum := by decide
  have hdescent : baseEnd_3993855 < baseStart_3993855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993879 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 5]
def baseStart_3993879 : Nat := 118140960795 + 3993879 * 2 ^ 59
def prefixEnd_3993879 : Nat := 4983230072969 + 3 ^ 40 * 3993879 * 2
def baseEnd_3993879 : Nat := 227864400322031629304999

theorem tailTrace_3993879 : CollatzResearch.WordTrace tailWord_3993879 prefixEnd_3993879 227864400322031629304999 := by
  unfold tailWord_3993879
  simp only [CollatzResearch.WordTrace]
  refine ⟨145668734297865958073536691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97112489531910638715691127 145668734297865958073536691)
  ·
    refine ⟨218503101446798937110305037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145668734297865958073536691 218503101446798937110305037)
    ·
      refine ⟨81938663042549601416364389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218503101446798937110305037 81938663042549601416364389)
      ·
        refine ⟨15363499320478050265568323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81938663042549601416364389 15363499320478050265568323)
        ·
          refine ⟨23045248980717075398352485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363499320478050265568323 23045248980717075398352485)
          ·
            refine ⟨4320984183884451637191091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23045248980717075398352485 4320984183884451637191091)
            ·
              refine ⟨6481476275826677455786637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4320984183884451637191091 6481476275826677455786637)
              ·
                refine ⟨2430553603435004045919989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6481476275826677455786637 2430553603435004045919989)
                ·
                  refine ⟨227864400322031629304999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2430553603435004045919989 227864400322031629304999)
                  ·
                    rfl

theorem cell23_3993879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 5].length) (baseStart_3993879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993879 prefixEnd_3993879 := by exact prefixLift 3993879
  have htrace : WordTrace (prefixWord ++ tailWord_3993879) baseStart_3993879 baseEnd_3993879 := by
    simpa [prefixWord, tailWord_3993879, baseEnd_3993879] using wordTrace_append hprefix tailTrace_3993879
  have hstable : (prefixWord ++ tailWord_3993879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993879).length < 2 ^ (prefixWord ++ tailWord_3993879).sum := by decide
  have hdescent : baseEnd_3993879 < baseStart_3993879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993892 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_3993892 : Nat := 118140960795 + 3993892 * 2 ^ 59
def prefixEnd_3993892 : Nat := 4983230072969 + 3 ^ 40 * 3993892 * 2
def baseEnd_3993892 : Nat := 683595426048931037627477

theorem tailTrace_3993892 : CollatzResearch.WordTrace tailWord_3993892 prefixEnd_3993892 683595426048931037627477 := by
  unfold tailWord_3993892
  simp only [CollatzResearch.WordTrace]
  refine ⟨72834604223409430646879965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97112805631212574195839953 72834604223409430646879965)
  ·
    refine ⟨27312976583778536492579987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72834604223409430646879965 27312976583778536492579987)
    ·
      refine ⟨40969464875667804738869981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27312976583778536492579987 40969464875667804738869981)
      ·
        refine ⟨15363549328375426777076243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40969464875667804738869981 15363549328375426777076243)
        ·
          refine ⟨23045323992563140165614365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15363549328375426777076243 23045323992563140165614365)
          ·
            refine ⟨8641996497211177562105387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23045323992563140165614365 8641996497211177562105387)
            ·
              refine ⟨12962994745816766343158081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8641996497211177562105387 12962994745816766343158081)
              ·
                refine ⟨9722246059362574757368561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12962994745816766343158081 9722246059362574757368561)
                ·
                  refine ⟨7291684544521931068026421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9722246059362574757368561 7291684544521931068026421)
                  ·
                    refine ⟨683595426048931037627477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7291684544521931068026421 683595426048931037627477)
                    ·
                      rfl

theorem cell23_3993892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_3993892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993892 prefixEnd_3993892 := by exact prefixLift 3993892
  have htrace : WordTrace (prefixWord ++ tailWord_3993892) baseStart_3993892 baseEnd_3993892 := by
    simpa [prefixWord, tailWord_3993892, baseEnd_3993892] using wordTrace_append hprefix tailTrace_3993892
  have hstable : (prefixWord ++ tailWord_3993892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993892).length < 2 ^ (prefixWord ++ tailWord_3993892).sum := by decide
  have hdescent : baseEnd_3993892 < baseStart_3993892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993896 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 5]
def baseStart_3993896 : Nat := 118140960795 + 3993896 * 2 ^ 59
def prefixEnd_3993896 : Nat := 4983230072969 + 3 ^ 40 * 3993896 * 2
def baseEnd_3993896 : Nat := 227865370229934566359157

theorem tailTrace_3993896 : CollatzResearch.WordTrace tailWord_3993896 prefixEnd_3993896 227865370229934566359157 := by
  unfold tailWord_3993896
  simp only [CollatzResearch.WordTrace]
  refine ⟨72834677169402184988452771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97112902892536246651270361 72834677169402184988452771)
  ·
    refine ⟨109252015754103277482679157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72834677169402184988452771 109252015754103277482679157)
    ·
      refine ⟨10242376476947182264001171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109252015754103277482679157 10242376476947182264001171)
      ·
        refine ⟨15363564715420773396001757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10242376476947182264001171 15363564715420773396001757)
        ·
          refine ⟨5761336768282790023500659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15363564715420773396001757 5761336768282790023500659)
          ·
            refine ⟨8642005152424185035250989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761336768282790023500659 8642005152424185035250989)
            ·
              refine ⟨3240751932159069388219121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8642005152424185035250989 3240751932159069388219121)
              ·
                refine ⟨2430563949119302041164341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240751932159069388219121 2430563949119302041164341)
                ·
                  refine ⟨227865370229934566359157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2430563949119302041164341 227865370229934566359157)
                  ·
                    rfl

theorem cell23_3993896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 5].length) (baseStart_3993896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993896 prefixEnd_3993896 := by exact prefixLift 3993896
  have htrace : WordTrace (prefixWord ++ tailWord_3993896) baseStart_3993896 baseEnd_3993896 := by
    simpa [prefixWord, tailWord_3993896, baseEnd_3993896] using wordTrace_append hprefix tailTrace_3993896
  have hstable : (prefixWord ++ tailWord_3993896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993896).length < 2 ^ (prefixWord ++ tailWord_3993896).sum := by decide
  have hdescent : baseEnd_3993896 < baseStart_3993896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993912 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_3993912 : Nat := 118140960795 + 3993912 * 2 ^ 59
def prefixEnd_3993912 : Nat := 4983230072969 + 3 ^ 40 * 3993912 * 2
def baseEnd_3993912 : Nat := 2050796547759883034632339

theorem tailTrace_3993912 : CollatzResearch.WordTrace tailWord_3993912 prefixEnd_3993912 2050796547759883034632339 := by
  unfold tailWord_3993912
  simp only [CollatzResearch.WordTrace]
  refine ⟨72834968953373202354743995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97113291937830936472991993 72834968953373202354743995)
  ·
    refine ⟨109252453430059803532115993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72834968953373202354743995 109252453430059803532115993)
    ·
      refine ⟨81939340072544852649086995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109252453430059803532115993 81939340072544852649086995)
      ·
        refine ⟨122909010108817278973630493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81939340072544852649086995 122909010108817278973630493)
        ·
          refine ⟨46090878790806479615111435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122909010108817278973630493 46090878790806479615111435)
          ·
            refine ⟨69136318186209719422667153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46090878790806479615111435 69136318186209719422667153)
            ·
              refine ⟨51852238639657289567000365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69136318186209719422667153 51852238639657289567000365)
              ·
                refine ⟨19444589489871483587625137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51852238639657289567000365 19444589489871483587625137)
                ·
                  refine ⟨14583442117403612690718853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19444589489871483587625137 14583442117403612690718853)
                  ·
                    refine ⟨2734395397013177379509785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14583442117403612690718853 2734395397013177379509785)
                    ·
                      refine ⟨2050796547759883034632339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734395397013177379509785 2050796547759883034632339)
                      ·
                        rfl

theorem cell23_3993912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_3993912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993912 prefixEnd_3993912 := by exact prefixLift 3993912
  have htrace : WordTrace (prefixWord ++ tailWord_3993912) baseStart_3993912 baseEnd_3993912 := by
    simpa [prefixWord, tailWord_3993912, baseEnd_3993912] using wordTrace_append hprefix tailTrace_3993912
  have hstable : (prefixWord ++ tailWord_3993912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993912).length < 2 ^ (prefixWord ++ tailWord_3993912).sum := by decide
  have hdescent : baseEnd_3993912 < baseStart_3993912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993955 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3993955 : Nat := 118140960795 + 3993955 * 2 ^ 59
def prefixEnd_3993955 : Nat := 4983230072969 + 3 ^ 40 * 3993955 * 2
def baseEnd_3993955 : Nat := 2050818627428026366394641

theorem tailTrace_3993955 : CollatzResearch.WordTrace tailWord_3993955 prefixEnd_3993955 2050818627428026366394641 := by
  unfold tailWord_3993955
  simp only [CollatzResearch.WordTrace]
  refine ⟨145671506245590623053303319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97114337497060415368868879 145671506245590623053303319)
  ·
    refine ⟨218507259368385934579954979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145671506245590623053303319 218507259368385934579954979)
    ·
      refine ⟨327760889052578901869932469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218507259368385934579954979 327760889052578901869932469)
      ·
        refine ⟨30727583348679272050306169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 327760889052578901869932469 30727583348679272050306169)
        ·
          refine ⟨23045687511509454037729627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30727583348679272050306169 23045687511509454037729627)
          ·
            refine ⟨34568531267264181056594441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23045687511509454037729627 34568531267264181056594441)
            ·
              refine ⟨25926398450448135792445831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34568531267264181056594441 25926398450448135792445831)
              ·
                refine ⟨38889597675672203688668747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25926398450448135792445831 38889597675672203688668747)
                ·
                  refine ⟨58334396513508305533003121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38889597675672203688668747 58334396513508305533003121)
                  ·
                    refine ⟨43750797385131229149752341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58334396513508305533003121 43750797385131229149752341)
                    ·
                      refine ⟨2050818627428026366394641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43750797385131229149752341 2050818627428026366394641)
                      ·
                        rfl

theorem cell23_3993955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3993955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993955 prefixEnd_3993955 := by exact prefixLift 3993955
  have htrace : WordTrace (prefixWord ++ tailWord_3993955) baseStart_3993955 baseEnd_3993955 := by
    simpa [prefixWord, tailWord_3993955, baseEnd_3993955] using wordTrace_append hprefix tailTrace_3993955
  have hstable : (prefixWord ++ tailWord_3993955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993955).length < 2 ^ (prefixWord ++ tailWord_3993955).sum := by decide
  have hdescent : baseEnd_3993955 < baseStart_3993955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993979 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 3]
def baseStart_3993979 : Nat := 118140960795 + 3993979 * 2 ^ 59
def prefixEnd_3993979 : Nat := 4983230072969 + 3 ^ 40 * 3993979 * 2
def baseEnd_3993979 : Nat := 2050830950963734272494531

theorem tailTrace_3993979 : CollatzResearch.WordTrace tailWord_3993979 prefixEnd_3993979 2050830950963734272494531 := by
  unfold tailWord_3993979
  simp only [CollatzResearch.WordTrace]
  refine ⟨145672381597503675152176991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97114921065002450101451327 145672381597503675152176991)
  ·
    refine ⟨218508572396255512728265487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145672381597503675152176991 218508572396255512728265487)
    ·
      refine ⟨327762858594383269092398231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218508572396255512728265487 327762858594383269092398231)
      ·
        refine ⟨491644287891574903638597347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327762858594383269092398231 491644287891574903638597347)
        ·
          refine ⟨737466431837362355457896021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491644287891574903638597347 737466431837362355457896021)
          ·
            refine ⟨8642184748094090103022219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 737466431837362355457896021 8642184748094090103022219)
            ·
              refine ⟨12963277122141135154533329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642184748094090103022219 12963277122141135154533329)
              ·
                refine ⟨9722457841605851365899997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12963277122141135154533329 9722457841605851365899997)
                ·
                  refine ⟨3645921690602194262212499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9722457841605851365899997 3645921690602194262212499)
                  ·
                    refine ⟨5468882535903291393318749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645921690602194262212499 5468882535903291393318749)
                    ·
                      refine ⟨2050830950963734272494531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468882535903291393318749 2050830950963734272494531)
                      ·
                        rfl

theorem cell23_3993979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 3].length) (baseStart_3993979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993979 prefixEnd_3993979 := by exact prefixLift 3993979
  have htrace : WordTrace (prefixWord ++ tailWord_3993979) baseStart_3993979 baseEnd_3993979 := by
    simpa [prefixWord, tailWord_3993979, baseEnd_3993979] using wordTrace_append hprefix tailTrace_3993979
  have hstable : (prefixWord ++ tailWord_3993979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993979).length < 2 ^ (prefixWord ++ tailWord_3993979).sum := by decide
  have hdescent : baseEnd_3993979 < baseStart_3993979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3993996 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 1, 1, 3]
def baseStart_3993996 : Nat := 118140960795 + 3993996 * 2 ^ 59
def prefixEnd_3993996 : Nat := 4983230072969 + 3 ^ 40 * 3993996 * 2
def baseEnd_3993996 : Nat := 2050839680134860705981953

theorem tailTrace_3993996 : CollatzResearch.WordTrace tailWord_3993996 prefixEnd_3993996 2050839680134860705981953 := by
  unfold tailWord_3993996
  simp only [CollatzResearch.WordTrace]
  refine ⟨72836500819221043527772921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97115334425628058037030561 72836500819221043527772921)
  ·
    refine ⟨54627375614415782645829691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72836500819221043527772921 54627375614415782645829691)
    ·
      refine ⟨81941063421623673968744537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54627375614415782645829691 81941063421623673968744537)
      ·
        refine ⟨61455797566217755476558403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81941063421623673968744537 61455797566217755476558403)
        ·
          refine ⟨92183696349326633214837605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61455797566217755476558403 92183696349326633214837605)
          ·
            refine ⟨17284443065498743727782051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92183696349326633214837605 17284443065498743727782051)
            ·
              refine ⟨25926664598248115591673077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17284443065498743727782051 25926664598248115591673077)
              ·
                refine ⟨2430624806085760836719351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25926664598248115591673077 2430624806085760836719351)
                ·
                  refine ⟨3645937209128641255079027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430624806085760836719351 3645937209128641255079027)
                  ·
                    refine ⟨5468905813692961882618541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3645937209128641255079027 5468905813692961882618541)
                    ·
                      refine ⟨2050839680134860705981953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468905813692961882618541 2050839680134860705981953)
                      ·
                        rfl

theorem cell23_3993996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_3993996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3993996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3993996 prefixEnd_3993996 := by exact prefixLift 3993996
  have htrace : WordTrace (prefixWord ++ tailWord_3993996) baseStart_3993996 baseEnd_3993996 := by
    simpa [prefixWord, tailWord_3993996, baseEnd_3993996] using wordTrace_append hprefix tailTrace_3993996
  have hstable : (prefixWord ++ tailWord_3993996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3993996).length < 2 ^ (prefixWord ++ tailWord_3993996).sum := by decide
  have hdescent : baseEnd_3993996 < baseStart_3993996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3993996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994039 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_3994039 : Nat := 118140960795 + 3994039 * 2 ^ 59
def prefixEnd_3994039 : Nat := 4983230072969 + 3 ^ 40 * 3994039 * 2
def baseEnd_3994039 : Nat := 2050861759803004037744255

theorem tailTrace_3994039 : CollatzResearch.WordTrace tailWord_3994039 prefixEnd_3994039 2050861759803004037744255 := by
  unfold tailWord_3994039
  simp only [CollatzResearch.WordTrace]
  refine ⟨145674569977286305399361171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97116379984857536932907447 145674569977286305399361171)
  ·
    refine ⟨218511854965929458099041757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145674569977286305399361171 218511854965929458099041757)
    ·
      refine ⟨81941945612223546787140659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218511854965929458099041757 81941945612223546787140659)
      ·
        refine ⟨122912918418335320180710989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81941945612223546787140659 122912918418335320180710989)
        ·
          refine ⟨46092344406875745067766621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122912918418335320180710989 46092344406875745067766621)
          ·
            refine ⟨17284629152578404400412483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46092344406875745067766621 17284629152578404400412483)
            ·
              refine ⟨25926943728867606600618725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17284629152578404400412483 25926943728867606600618725)
              ·
                refine ⟨4861301949162676237616011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25926943728867606600618725 4861301949162676237616011)
                ·
                  refine ⟨7291952923744014356424017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861301949162676237616011 7291952923744014356424017)
                  ·
                    refine ⟨5468964692808010767318013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7291952923744014356424017 5468964692808010767318013)
                    ·
                      refine ⟨2050861759803004037744255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5468964692808010767318013 2050861759803004037744255)
                      ·
                        rfl

theorem cell23_3994039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_3994039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994039 prefixEnd_3994039 := by exact prefixLift 3994039
  have htrace : WordTrace (prefixWord ++ tailWord_3994039) baseStart_3994039 baseEnd_3994039 := by
    simpa [prefixWord, tailWord_3994039, baseEnd_3994039] using wordTrace_append hprefix tailTrace_3994039
  have hstable : (prefixWord ++ tailWord_3994039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994039).length < 2 ^ (prefixWord ++ tailWord_3994039).sum := by decide
  have hdescent : baseEnd_3994039 < baseStart_3994039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994112 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_3994112 : Nat := 118140960795 + 3994112 * 2 ^ 59
def prefixEnd_3994112 : Nat := 4983230072969 + 3 ^ 40 * 3994112 * 2
def baseEnd_3994112 : Nat := 2050899243890782252131419

theorem tailTrace_3994112 : CollatzResearch.WordTrace tailWord_3994112 prefixEnd_3994112 2050899243890782252131419 := by
  unfold tailWord_3994112
  simp only [CollatzResearch.WordTrace]
  refine ⟨72838616253010919433384295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97118155004014559244512393 72838616253010919433384295)
  ·
    refine ⟨109257924379516379150076443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72838616253010919433384295 109257924379516379150076443)
    ·
      refine ⟨163886886569274568725114665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109257924379516379150076443 163886886569274568725114665)
      ·
        refine ⟨122915164926955926543835999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163886886569274568725114665 122915164926955926543835999)
        ·
          refine ⟨184372747390433889815753999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122915164926955926543835999 184372747390433889815753999)
          ·
            refine ⟨276559121085650834723630999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184372747390433889815753999 276559121085650834723630999)
            ·
              refine ⟨414838681628476252085446499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276559121085650834723630999 414838681628476252085446499)
              ·
                refine ⟨622258022442714378128169749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414838681628476252085446499 622258022442714378128169749)
                ·
                  refine ⟨29168344802002236474757957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 622258022442714378128169749 29168344802002236474757957)
                  ·
                    refine ⟨5469064650375419339017117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29168344802002236474757957 5469064650375419339017117)
                    ·
                      refine ⟨2050899243890782252131419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5469064650375419339017117 2050899243890782252131419)
                      ·
                        rfl

theorem cell23_3994112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_3994112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994112 prefixEnd_3994112 := by exact prefixLift 3994112
  have htrace : WordTrace (prefixWord ++ tailWord_3994112) baseStart_3994112 baseEnd_3994112 := by
    simpa [prefixWord, tailWord_3994112, baseEnd_3994112] using wordTrace_append hprefix tailTrace_3994112
  have hstable : (prefixWord ++ tailWord_3994112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994112).length < 2 ^ (prefixWord ++ tailWord_3994112).sum := by decide
  have hdescent : baseEnd_3994112 < baseStart_3994112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994164 : List Nat := [2, 5, 1, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3994164 : Nat := 118140960795 + 3994164 * 2 ^ 59
def prefixEnd_3994164 : Nat := 4983230072969 + 3 ^ 40 * 3994164 * 2
def baseEnd_3994164 : Nat := 2050925944884816048681181

theorem tailTrace_3994164 : CollatzResearch.WordTrace tailWord_3994164 prefixEnd_3994164 2050925944884816048681181 := by
  unfold tailWord_3994164
  simp only [CollatzResearch.WordTrace]
  refine ⟨72839564550916725873830773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97119419401222301165107697 72839564550916725873830773)
  ·
    refine ⟨6828709176648443050671635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72839564550916725873830773 6828709176648443050671635)
    ·
      refine ⟨10243063764972664576007453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828709176648443050671635 10243063764972664576007453)
      ·
        refine ⟨3841148911864749216002795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10243063764972664576007453 3841148911864749216002795)
        ·
          refine ⟨5761723367797123824004193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841148911864749216002795 5761723367797123824004193)
          ·
            refine ⟨4321292525847842868003145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5761723367797123824004193 4321292525847842868003145)
            ·
              refine ⟨3240969394385882151002359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4321292525847842868003145 3240969394385882151002359)
              ·
                refine ⟨4861454091578823226503539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3240969394385882151002359 4861454091578823226503539)
                ·
                  refine ⟨7292181137368234839755309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861454091578823226503539 7292181137368234839755309)
                  ·
                    refine ⟨2734567926513088064908241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7292181137368234839755309 2734567926513088064908241)
                    ·
                      refine ⟨2050925944884816048681181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734567926513088064908241 2050925944884816048681181)
                      ·
                        rfl

theorem cell23_3994164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3994164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994164 prefixEnd_3994164 := by exact prefixLift 3994164
  have htrace : WordTrace (prefixWord ++ tailWord_3994164) baseStart_3994164 baseEnd_3994164 := by
    simpa [prefixWord, tailWord_3994164, baseEnd_3994164] using wordTrace_append hprefix tailTrace_3994164
  have hstable : (prefixWord ++ tailWord_3994164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994164).length < 2 ^ (prefixWord ++ tailWord_3994164).sum := by decide
  have hdescent : baseEnd_3994164 < baseStart_3994164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994300 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3994300 : Nat := 118140960795 + 3994300 * 2 ^ 59
def prefixEnd_3994300 : Nat := 4983230072969 + 3 ^ 40 * 3994300 * 2
def baseEnd_3994300 : Nat := 2050995778253827516580555

theorem tailTrace_3994300 : CollatzResearch.WordTrace tailWord_3994300 prefixEnd_3994300 2050995778253827516580555 := by
  unfold tailWord_3994300
  simp only [CollatzResearch.WordTrace]
  refine ⟨72842044714670373487306177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97122726286227164649741569 72842044714670373487306177)
  ·
    refine ⟨54631533536002780115479633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72842044714670373487306177 54631533536002780115479633)
    ·
      refine ⟨40973650152002085086609725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54631533536002780115479633 40973650152002085086609725)
      ·
        refine ⟨15365118807000781907478647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40973650152002085086609725 15365118807000781907478647)
        ·
          refine ⟨23047678210501172861217971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15365118807000781907478647 23047678210501172861217971)
          ·
            refine ⟨34571517315751759291826957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23047678210501172861217971 34571517315751759291826957)
            ·
              refine ⟨12964318993406909734435109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34571517315751759291826957 12964318993406909734435109)
              ·
                refine ⟨2430809811263795575206583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12964318993406909734435109 2430809811263795575206583)
                ·
                  refine ⟨3646214716895693362809875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430809811263795575206583 3646214716895693362809875)
                  ·
                    refine ⟨5469322075343540044214813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646214716895693362809875 5469322075343540044214813)
                    ·
                      refine ⟨2050995778253827516580555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5469322075343540044214813 2050995778253827516580555)
                      ·
                        rfl

theorem cell23_3994300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3994300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994300 prefixEnd_3994300 := by exact prefixLift 3994300
  have htrace : WordTrace (prefixWord ++ tailWord_3994300) baseStart_3994300 baseEnd_3994300 := by
    simpa [prefixWord, tailWord_3994300, baseEnd_3994300] using wordTrace_append hprefix tailTrace_3994300
  have hstable : (prefixWord ++ tailWord_3994300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994300).length < 2 ^ (prefixWord ++ tailWord_3994300).sum := by decide
  have hdescent : baseEnd_3994300 < baseStart_3994300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994309 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_3994309 : Nat := 118140960795 + 3994309 * 2 ^ 59
def prefixEnd_3994309 : Nat := 4983230072969 + 3 ^ 40 * 3994309 * 2
def baseEnd_3994309 : Nat := 2051000399579717981368013

theorem tailTrace_3994309 : CollatzResearch.WordTrace tailWord_3994309 prefixEnd_3994309 2051000399579717981368013 := by
  unfold tailWord_3994309
  simp only [CollatzResearch.WordTrace]
  refine ⟨145684417686308141511689981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97122945124205427674459987 145684417686308141511689981)
  ·
    refine ⟨54631656632365553066883743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145684417686308141511689981 54631656632365553066883743)
    ·
      refine ⟨81947484948548329600325615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54631656632365553066883743 81947484948548329600325615)
      ·
        refine ⟨122921227422822494400488423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81947484948548329600325615 122921227422822494400488423)
        ·
          refine ⟨184381841134233741600732635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122921227422822494400488423 184381841134233741600732635)
          ·
            refine ⟨276572761701350612401098953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184381841134233741600732635 276572761701350612401098953)
            ·
              refine ⟨207429571276012959300824215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276572761701350612401098953 207429571276012959300824215)
              ·
                refine ⟨311144356914019438951236323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207429571276012959300824215 311144356914019438951236323)
                ·
                  refine ⟨466716535371029158426854485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311144356914019438951236323 466716535371029158426854485)
                  ·
                    refine ⟨5469334398879247950314701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 466716535371029158426854485 5469334398879247950314701)
                    ·
                      refine ⟨2051000399579717981368013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5469334398879247950314701 2051000399579717981368013)
                      ·
                        rfl

theorem cell23_3994309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_3994309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994309 prefixEnd_3994309 := by exact prefixLift 3994309
  have htrace : WordTrace (prefixWord ++ tailWord_3994309) baseStart_3994309 baseEnd_3994309 := by
    simpa [prefixWord, tailWord_3994309, baseEnd_3994309] using wordTrace_append hprefix tailTrace_3994309
  have hstable : (prefixWord ++ tailWord_3994309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994309).length < 2 ^ (prefixWord ++ tailWord_3994309).sum := by decide
  have hdescent : baseEnd_3994309 < baseStart_3994309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994316 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_3994316 : Nat := 118140960795 + 3994316 * 2 ^ 59
def prefixEnd_3994316 : Nat := 4983230072969 + 3 ^ 40 * 3994316 * 2
def baseEnd_3994316 : Nat := 683667997981433151326827

theorem tailTrace_3994316 : CollatzResearch.WordTrace tailWord_3994316 prefixEnd_3994316 683667997981433151326827 := by
  unfold tailWord_3994316
  simp only [CollatzResearch.WordTrace]
  refine ⟨72842336498641390853597401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97123115331521854471463201 72842336498641390853597401)
  ·
    refine ⟨54631752373981043140198051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72842336498641390853597401 54631752373981043140198051)
    ·
      refine ⟨81947628560971564710297077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54631752373981043140198051 81947628560971564710297077)
      ·
        refine ⟨7682590177591084191590351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81947628560971564710297077 7682590177591084191590351)
        ·
          refine ⟨11523885266386626287385527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682590177591084191590351 11523885266386626287385527)
          ·
            refine ⟨17285827899579939431078291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523885266386626287385527 17285827899579939431078291)
            ·
              refine ⟨25928741849369909146617437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17285827899579939431078291 25928741849369909146617437)
              ·
                refine ⟨9723278193513715929981539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25928741849369909146617437 9723278193513715929981539)
                ·
                  refine ⟨14584917290270573894972309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723278193513715929981539 14584917290270573894972309)
                  ·
                    refine ⟨683667997981433151326827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14584917290270573894972309 683667997981433151326827)
                    ·
                      rfl

theorem cell23_3994316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_3994316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994316 prefixEnd_3994316 := by exact prefixLift 3994316
  have htrace : WordTrace (prefixWord ++ tailWord_3994316) baseStart_3994316 baseEnd_3994316 := by
    simpa [prefixWord, tailWord_3994316, baseEnd_3994316] using wordTrace_append hprefix tailTrace_3994316
  have hstable : (prefixWord ++ tailWord_3994316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994316).length < 2 ^ (prefixWord ++ tailWord_3994316).sum := by decide
  have hdescent : baseEnd_3994316 < baseStart_3994316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994317 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3994317 : Nat := 118140960795 + 3994317 * 2 ^ 59
def prefixEnd_3994317 : Nat := 4983230072969 + 3 ^ 40 * 3994317 * 2
def baseEnd_3994317 : Nat := 2051004507424953950067977

theorem tailTrace_3994317 : CollatzResearch.WordTrace tailWord_3994317 prefixEnd_3994317 2051004507424953950067977 := by
  unfold tailWord_3994317
  simp only [CollatzResearch.WordTrace]
  refine ⟨145684709470279158877981205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97123139646852772585320803 145684709470279158877981205)
  ·
    refine ⟨6828970756419335572405369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145684709470279158877981205 6828970756419335572405369)
    ·
      refine ⟨5121728067314501679304027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6828970756419335572405369 5121728067314501679304027)
      ·
        refine ⟨7682592100971752518956041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121728067314501679304027 7682592100971752518956041)
        ·
          refine ⟨5761944075728814389217031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682592100971752518956041 5761944075728814389217031)
          ·
            refine ⟨8642916113593221583825547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761944075728814389217031 8642916113593221583825547)
            ·
              refine ⟨12964374170389832375738321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642916113593221583825547 12964374170389832375738321)
              ·
                refine ⟨9723280627792374281803741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12964374170389832375738321 9723280627792374281803741)
                ·
                  refine ⟨3646230235422140355676403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9723280627792374281803741 3646230235422140355676403)
                  ·
                    refine ⟨5469345353133210533514605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646230235422140355676403 5469345353133210533514605)
                    ·
                      refine ⟨2051004507424953950067977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5469345353133210533514605 2051004507424953950067977)
                      ·
                        rfl

theorem cell23_3994317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3994317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994317 prefixEnd_3994317 := by exact prefixLift 3994317
  have htrace : WordTrace (prefixWord ++ tailWord_3994317) baseStart_3994317 baseEnd_3994317 := by
    simpa [prefixWord, tailWord_3994317, baseEnd_3994317] using wordTrace_append hprefix tailTrace_3994317
  have hstable : (prefixWord ++ tailWord_3994317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994317).length < 2 ^ (prefixWord ++ tailWord_3994317).sum := by decide
  have hdescent : baseEnd_3994317 < baseStart_3994317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994340 : List Nat := [2, 3, 1, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_3994340 : Nat := 118140960795 + 3994340 * 2 ^ 59
def prefixEnd_3994340 : Nat := 4983230072969 + 3 ^ 40 * 3994340 * 2
def baseEnd_3994340 : Nat := 2051016317480007360080371

theorem tailTrace_3994340 : CollatzResearch.WordTrace tailWord_3994340 prefixEnd_3994340 2051016317480007360080371 := by
  unfold tailWord_3994340
  simp only [CollatzResearch.WordTrace]
  refine ⟨72842774174597916903034237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97123698899463889204045649 72842774174597916903034237)
  ·
    refine ⟨27316040315474218838637839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72842774174597916903034237 27316040315474218838637839)
    ·
      refine ⟨40974060473211328257956759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27316040315474218838637839 40974060473211328257956759)
      ·
        refine ⟨61461090709816992386935139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40974060473211328257956759 61461090709816992386935139)
        ·
          refine ⟨92191636064725488580402709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61461090709816992386935139 92191636064725488580402709)
          ·
            refine ⟨4321482940534007277206377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92191636064725488580402709 4321482940534007277206377)
            ·
              refine ⟨3241112205400505457904783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4321482940534007277206377 3241112205400505457904783)
              ·
                refine ⟨4861668308100758186857175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241112205400505457904783 4861668308100758186857175)
                ·
                  refine ⟨7292502462151137280285763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861668308100758186857175 7292502462151137280285763)
                  ·
                    refine ⟨10938753693226705920428645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292502462151137280285763 10938753693226705920428645)
                    ·
                      refine ⟨2051016317480007360080371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10938753693226705920428645 2051016317480007360080371)
                      ·
                        rfl

theorem cell23_3994340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_3994340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994340 prefixEnd_3994340 := by exact prefixLift 3994340
  have htrace : WordTrace (prefixWord ++ tailWord_3994340) baseStart_3994340 baseEnd_3994340 := by
    simpa [prefixWord, tailWord_3994340, baseEnd_3994340] using wordTrace_append hprefix tailTrace_3994340
  have hstable : (prefixWord ++ tailWord_3994340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994340).length < 2 ^ (prefixWord ++ tailWord_3994340).sum := by decide
  have hdescent : baseEnd_3994340 < baseStart_3994340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994350 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3994350 : Nat := 118140960795 + 3994350 * 2 ^ 59
def prefixEnd_3994350 : Nat := 4983230072969 + 3 ^ 40 * 3994350 * 2
def baseEnd_3994350 : Nat := 683673817428850773651775

theorem tailTrace_3994350 : CollatzResearch.WordTrace tailWord_3994350 prefixEnd_3994350 683673817428850773651775 := by
  unfold tailWord_3994350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210739134894950689241563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97123942052773070342621669 18210739134894950689241563)
  ·
    refine ⟨27316108702342426033862345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18210739134894950689241563 27316108702342426033862345)
    ·
      refine ⟨20487081526756819525396759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27316108702342426033862345 20487081526756819525396759)
      ·
        refine ⟨30730622290135229288095139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20487081526756819525396759 30730622290135229288095139)
        ·
          refine ⟨46095933435202843932142709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30730622290135229288095139 46095933435202843932142709)
          ·
            refine ⟨4321493759550266618638379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46095933435202843932142709 4321493759550266618638379)
            ·
              refine ⟨6482240639325399927957569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321493759550266618638379 6482240639325399927957569)
              ·
                refine ⟨4861680479494049945968177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6482240639325399927957569 4861680479494049945968177)
                ·
                  refine ⟨3646260359620537459476133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861680479494049945968177 3646260359620537459476133)
                  ·
                    refine ⟨683673817428850773651775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646260359620537459476133 683673817428850773651775)
                    ·
                      rfl

theorem cell23_3994350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3994350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994350 prefixEnd_3994350 := by exact prefixLift 3994350
  have htrace : WordTrace (prefixWord ++ tailWord_3994350) baseStart_3994350 baseEnd_3994350 := by
    simpa [prefixWord, tailWord_3994350, baseEnd_3994350] using wordTrace_append hprefix tailTrace_3994350
  have hstable : (prefixWord ++ tailWord_3994350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994350).length < 2 ^ (prefixWord ++ tailWord_3994350).sum := by decide
  have hdescent : baseEnd_3994350 < baseStart_3994350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994370 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_3994370 : Nat := 118140960795 + 3994370 * 2 ^ 59
def prefixEnd_3994370 : Nat := 4983230072969 + 3 ^ 40 * 3994370 * 2
def baseEnd_3994370 : Nat := 2051031721899642242705233

theorem tailTrace_3994370 : CollatzResearch.WordTrace tailWord_3994370 prefixEnd_3994370 2051031721899642242705233 := by
  unfold tailWord_3994370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36421660634771787232415141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97124428359391432619773709 36421660634771787232415141)
  ·
    refine ⟨6829061369019710106077839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36421660634771787232415141 6829061369019710106077839)
    ·
      refine ⟨10243592053529565159116759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829061369019710106077839 10243592053529565159116759)
      ·
        refine ⟨15365388080294347738675139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10243592053529565159116759 15365388080294347738675139)
        ·
          refine ⟨23048082120441521608012709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15365388080294347738675139 23048082120441521608012709)
          ·
            refine ⟨4321515397582785301502383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23048082120441521608012709 4321515397582785301502383)
            ·
              refine ⟨6482273096374177952253575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321515397582785301502383 6482273096374177952253575)
              ·
                refine ⟨9723409644561266928380363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482273096374177952253575 9723409644561266928380363)
                ·
                  refine ⟨14585114466841900392570545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9723409644561266928380363 14585114466841900392570545)
                  ·
                    refine ⟨10938835850131425294427909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14585114466841900392570545 10938835850131425294427909)
                    ·
                      refine ⟨2051031721899642242705233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10938835850131425294427909 2051031721899642242705233)
                      ·
                        rfl

theorem cell23_3994370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_3994370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994370 prefixEnd_3994370 := by exact prefixLift 3994370
  have htrace : WordTrace (prefixWord ++ tailWord_3994370) baseStart_3994370 baseEnd_3994370 := by
    simpa [prefixWord, tailWord_3994370, baseEnd_3994370] using wordTrace_append hprefix tailTrace_3994370
  have hstable : (prefixWord ++ tailWord_3994370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994370).length < 2 ^ (prefixWord ++ tailWord_3994370).sum := by decide
  have hdescent : baseEnd_3994370 < baseStart_3994370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994373 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_3994373 : Nat := 118140960795 + 3994373 * 2 ^ 59
def prefixEnd_3994373 : Nat := 4983230072969 + 3 ^ 40 * 3994373 * 2
def baseEnd_3994373 : Nat := 2051033262341605730967719

theorem tailTrace_3994373 : CollatzResearch.WordTrace tailWord_3994373 prefixEnd_3994373 2051033262341605730967719 := by
  unfold tailWord_3994373
  simp only [CollatzResearch.WordTrace]
  refine ⟨145686751958076280442019773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97124501305384186961346515 145686751958076280442019773)
  ·
    refine ⟨54632531984278605165757415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145686751958076280442019773 54632531984278605165757415)
    ·
      refine ⟨81948797976417907748636123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54632531984278605165757415 81948797976417907748636123)
      ·
        refine ⟨122923196964626861622954185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81948797976417907748636123 122923196964626861622954185)
        ·
          refine ⟨92192397723470146217215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122923196964626861622954185 92192397723470146217215639)
          ·
            refine ⟨138288596585205219325823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92192397723470146217215639 138288596585205219325823459)
            ·
              refine ⟨207432894877807828988735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138288596585205219325823459 207432894877807828988735189)
              ·
                refine ⟨4861708473698620991923481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207432894877807828988735189 4861708473698620991923481)
                ·
                  refine ⟨3646281355273965743942611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4861708473698620991923481 3646281355273965743942611)
                  ·
                    refine ⟨5469422032910948615913917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646281355273965743942611 5469422032910948615913917)
                    ·
                      refine ⟨2051033262341605730967719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5469422032910948615913917 2051033262341605730967719)
                      ·
                        rfl

theorem cell23_3994373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_3994373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994373 prefixEnd_3994373 := by exact prefixLift 3994373
  have htrace : WordTrace (prefixWord ++ tailWord_3994373) baseStart_3994373 baseEnd_3994373 := by
    simpa [prefixWord, tailWord_3994373, baseEnd_3994373] using wordTrace_append hprefix tailTrace_3994373
  have hstable : (prefixWord ++ tailWord_3994373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994373).length < 2 ^ (prefixWord ++ tailWord_3994373).sum := by decide
  have hdescent : baseEnd_3994373 < baseStart_3994373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994391 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3994391 : Nat := 118140960795 + 3994391 * 2 ^ 59
def prefixEnd_3994391 : Nat := 4983230072969 + 3 ^ 40 * 3994391 * 2
def baseEnd_3994391 : Nat := 2051042504993386660542637

theorem tailTrace_3994391 : CollatzResearch.WordTrace tailWord_3994391 prefixEnd_3994391 2051042504993386660542637 := by
  unfold tailWord_3994391
  simp only [CollatzResearch.WordTrace]
  refine ⟨145687408472011069516175027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97124938981340713010783351 145687408472011069516175027)
  ·
    refine ⟨218531112708016604274262541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145687408472011069516175027 218531112708016604274262541)
    ·
      refine ⟨81949167265506226602848453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218531112708016604274262541 81949167265506226602848453)
      ·
        refine ⟨15365468862282417488034085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81949167265506226602848453 15365468862282417488034085)
        ·
          refine ⟨2881025411677953279006391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15365468862282417488034085 2881025411677953279006391)
          ·
            refine ⟨4321538117516929918509587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881025411677953279006391 4321538117516929918509587)
            ·
              refine ⟨6482307176275394877764381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321538117516929918509587 6482307176275394877764381)
              ·
                refine ⟨2430865191103273079161643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6482307176275394877764381 2430865191103273079161643)
                ·
                  refine ⟨3646297786654909618742465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2430865191103273079161643 3646297786654909618742465)
                  ·
                    refine ⟨2734723339991182214056849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3646297786654909618742465 2734723339991182214056849)
                    ·
                      refine ⟨2051042504993386660542637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734723339991182214056849 2051042504993386660542637)
                      ·
                        rfl

theorem cell23_3994391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3994391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994391 prefixEnd_3994391 := by exact prefixLift 3994391
  have htrace : WordTrace (prefixWord ++ tailWord_3994391) baseStart_3994391 baseEnd_3994391 := by
    simpa [prefixWord, tailWord_3994391, baseEnd_3994391] using wordTrace_append hprefix tailTrace_3994391
  have hstable : (prefixWord ++ tailWord_3994391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994391).length < 2 ^ (prefixWord ++ tailWord_3994391).sum := by decide
  have hdescent : baseEnd_3994391 < baseStart_3994391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994400 : List Nat := [2, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2]
def baseStart_3994400 : Nat := 118140960795 + 3994400 * 2 ^ 59
def prefixEnd_3994400 : Nat := 4983230072969 + 3 ^ 40 * 3994400 * 2
def baseEnd_3994400 : Nat := 2051047126319277125330095

theorem tailTrace_3994400 : CollatzResearch.WordTrace tailWord_3994400 prefixEnd_3994400 2051047126319277125330095 := by
  unfold tailWord_3994400
  simp only [CollatzResearch.WordTrace]
  refine ⟨72843868364489232026626327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97125157819318976035501769 72843868364489232026626327)
  ·
    refine ⟨109265802546733848039939491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72843868364489232026626327 109265802546733848039939491)
    ·
      refine ⟨163898703820100772059909237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109265802546733848039939491 163898703820100772059909237)
      ·
        refine ⟨15365503483134447380616491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163898703820100772059909237 15365503483134447380616491)
        ·
          refine ⟨23048255224701671070924737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15365503483134447380616491 23048255224701671070924737)
          ·
            refine ⟨17286191418526253303193553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23048255224701671070924737 17286191418526253303193553)
            ·
              refine ⟨12964643563894689977395165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17286191418526253303193553 12964643563894689977395165)
              ·
                refine ⟨4861741336460508741523187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12964643563894689977395165 4861741336460508741523187)
                ·
                  refine ⟨7292612004690763112284781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4861741336460508741523187 7292612004690763112284781)
                  ·
                    refine ⟨2734729501759036167106793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7292612004690763112284781 2734729501759036167106793)
                    ·
                      refine ⟨2051047126319277125330095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734729501759036167106793 2051047126319277125330095)
                      ·
                        rfl

theorem cell23_3994400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_3994400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994400 prefixEnd_3994400 := by exact prefixLift 3994400
  have htrace : WordTrace (prefixWord ++ tailWord_3994400) baseStart_3994400 baseEnd_3994400 := by
    simpa [prefixWord, tailWord_3994400, baseEnd_3994400] using wordTrace_append hprefix tailTrace_3994400
  have hstable : (prefixWord ++ tailWord_3994400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994400).length < 2 ^ (prefixWord ++ tailWord_3994400).sum := by decide
  have hdescent : baseEnd_3994400 < baseStart_3994400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994453 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 5]
def baseStart_3994453 : Nat := 118140960795 + 3994453 * 2 ^ 59
def prefixEnd_3994453 : Nat := 4983230072969 + 3 ^ 40 * 3994453 * 2
def baseEnd_3994453 : Nat := 227897148977107268663039

theorem tailTrace_3994453 : CollatzResearch.WordTrace tailWord_3994453 prefixEnd_3994453 227897148977107268663039 := by
  unfold tailWord_3994453
  simp only [CollatzResearch.WordTrace]
  refine ⟨145689669797786454104932013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97126446531857636069954675 145689669797786454104932013)
  ·
    refine ⟨54633626174169920289349505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145689669797786454104932013 54633626174169920289349505)
    ·
      refine ⟨40975219630627440217012129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54633626174169920289349505 40975219630627440217012129)
      ·
        refine ⟨30731414722970580162759097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40975219630627440217012129 30731414722970580162759097)
        ·
          refine ⟨23048561042227935122069323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30731414722970580162759097 23048561042227935122069323)
          ·
            refine ⟨34572841563341902683103985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23048561042227935122069323 34572841563341902683103985)
            ·
              refine ⟨25929631172506427012327989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34572841563341902683103985 25929631172506427012327989)
              ·
                refine ⟨2430902922422477532405749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25929631172506427012327989 2430902922422477532405749)
                ·
                  refine ⟨227897148977107268663039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2430902922422477532405749 227897148977107268663039)
                  ·
                    rfl

theorem cell23_3994453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_3994453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994453 prefixEnd_3994453 := by exact prefixLift 3994453
  have htrace : WordTrace (prefixWord ++ tailWord_3994453) baseStart_3994453 baseEnd_3994453 := by
    simpa [prefixWord, tailWord_3994453, baseEnd_3994453] using wordTrace_append hprefix tailTrace_3994453
  have hstable : (prefixWord ++ tailWord_3994453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994453).length < 2 ^ (prefixWord ++ tailWord_3994453).sum := by decide
  have hdescent : baseEnd_3994453 < baseStart_3994453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994476 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_3994476 : Nat := 118140960795 + 3994476 * 2 ^ 59
def prefixEnd_3994476 : Nat := 4983230072969 + 3 ^ 40 * 3994476 * 2
def baseEnd_3994476 : Nat := 2051086150849018827979745

theorem tailTrace_3994476 : CollatzResearch.WordTrace tailWord_3994476 prefixEnd_3994476 2051086150849018827979745 := by
  unfold tailWord_3994476
  simp only [CollatzResearch.WordTrace]
  refine ⟨72845254338351564516509641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97127005784468752688679521 72845254338351564516509641)
  ·
    refine ⟨54633940753763673387382231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72845254338351564516509641 54633940753763673387382231)
    ·
      refine ⟨81950911130645510081073347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54633940753763673387382231 81950911130645510081073347)
      ·
        refine ⟨122926366695968265121610021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81950911130645510081073347 122926366695968265121610021)
        ·
          refine ⟨23048693755494049710301879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122926366695968265121610021 23048693755494049710301879)
          ·
            refine ⟨34573040633241074565452819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23048693755494049710301879 34573040633241074565452819)
            ·
              refine ⟨51859560949861611848179229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34573040633241074565452819 51859560949861611848179229)
              ·
                refine ⟨19447335356198104443067211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51859560949861611848179229 19447335356198104443067211)
                ·
                  refine ⟨29171003034297156664600817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19447335356198104443067211 29171003034297156664600817)
                  ·
                    refine ⟨21878252275722867498450613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29171003034297156664600817 21878252275722867498450613)
                    ·
                      refine ⟨2051086150849018827979745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21878252275722867498450613 2051086150849018827979745)
                      ·
                        rfl

theorem cell23_3994476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_3994476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994476 prefixEnd_3994476 := by exact prefixLift 3994476
  have htrace : WordTrace (prefixWord ++ tailWord_3994476) baseStart_3994476 baseEnd_3994476 := by
    simpa [prefixWord, tailWord_3994476, baseEnd_3994476] using wordTrace_append hprefix tailTrace_3994476
  have hstable : (prefixWord ++ tailWord_3994476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994476).length < 2 ^ (prefixWord ++ tailWord_3994476).sum := by decide
  have hdescent : baseEnd_3994476 < baseStart_3994476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994503 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3994503 : Nat := 118140960795 + 3994503 * 2 ^ 59
def prefixEnd_3994503 : Nat := 4983230072969 + 3 ^ 40 * 3994503 * 2
def baseEnd_3994503 : Nat := 2051100014826690222342121

theorem tailTrace_3994503 : CollatzResearch.WordTrace tailWord_3994503 prefixEnd_3994503 2051100014826690222342121 := by
  unfold tailWord_3994503
  simp only [CollatzResearch.WordTrace]
  refine ⟨145691493447605312644252163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97127662298403541762834775 145691493447605312644252163)
  ·
    refine ⟨218537240171407968966378245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145691493447605312644252163 218537240171407968966378245)
    ·
      refine ⟨40975732532138994181195921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218537240171407968966378245 40975732532138994181195921)
      ·
        refine ⟨30731799399104245635896941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40975732532138994181195921 30731799399104245635896941)
        ·
          refine ⟨11524424774664092113461353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30731799399104245635896941 11524424774664092113461353)
          ·
            refine ⟨8643318580998069085096015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11524424774664092113461353 8643318580998069085096015)
            ·
              refine ⟨12964977871497103627644023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8643318580998069085096015 12964977871497103627644023)
              ·
                refine ⟨19447466807245655441466035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12964977871497103627644023 19447466807245655441466035)
                ·
                  refine ⟨29171200210868483162199053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19447466807245655441466035 29171200210868483162199053)
                  ·
                    refine ⟨10939200079075681185824645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29171200210868483162199053 10939200079075681185824645)
                    ·
                      refine ⟨2051100014826690222342121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10939200079075681185824645 2051100014826690222342121)
                      ·
                        rfl

theorem cell23_3994503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3994503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994503 prefixEnd_3994503 := by exact prefixLift 3994503
  have htrace : WordTrace (prefixWord ++ tailWord_3994503) baseStart_3994503 baseEnd_3994503 := by
    simpa [prefixWord, tailWord_3994503, baseEnd_3994503] using wordTrace_append hprefix tailTrace_3994503
  have hstable : (prefixWord ++ tailWord_3994503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994503).length < 2 ^ (prefixWord ++ tailWord_3994503).sum := by decide
  have hdescent : baseEnd_3994503 < baseStart_3994503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994530 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3994530 : Nat := 118140960795 + 3994530 * 2 ^ 59
def prefixEnd_3994530 : Nat := 4983230072969 + 3 ^ 40 * 3994530 * 2
def baseEnd_3994530 : Nat := 683704626268120538901499

theorem tailTrace_3994530 : CollatzResearch.WordTrace tailWord_3994530 prefixEnd_3994530 683704626268120538901499 := by
  unfold tailWord_3994530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36423119554626874063871261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97128318812338330836990029 36423119554626874063871261)
  ·
    refine ⟨13658669832985077773951723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36423119554626874063871261 13658669832985077773951723)
    ·
      refine ⟨20488004749477616660927585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13658669832985077773951723 20488004749477616660927585)
      ·
        refine ⟨15366003562108212495695689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20488004749477616660927585 15366003562108212495695689)
        ·
          refine ⟨11524502671581159371771767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15366003562108212495695689 11524502671581159371771767)
          ·
            refine ⟨17286754007371739057657651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11524502671581159371771767 17286754007371739057657651)
            ·
              refine ⟨25930131011057608586486477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17286754007371739057657651 25930131011057608586486477)
              ·
                refine ⟨9723799129146603219932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25930131011057608586486477 9723799129146603219932429)
                ·
                  refine ⟨3646424673429976207474661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9723799129146603219932429 3646424673429976207474661)
                  ·
                    refine ⟨683704626268120538901499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646424673429976207474661 683704626268120538901499)
                    ·
                      rfl

theorem cell23_3994530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3994530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994530 prefixEnd_3994530 := by exact prefixLift 3994530
  have htrace : WordTrace (prefixWord ++ tailWord_3994530) baseStart_3994530 baseEnd_3994530 := by
    simpa [prefixWord, tailWord_3994530, baseEnd_3994530] using wordTrace_append hprefix tailTrace_3994530
  have hstable : (prefixWord ++ tailWord_3994530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994530).length < 2 ^ (prefixWord ++ tailWord_3994530).sum := by decide
  have hdescent : baseEnd_3994530 < baseStart_3994530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994593 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3994593 : Nat := 118140960795 + 3994593 * 2 ^ 59
def prefixEnd_3994593 : Nat := 4983230072969 + 3 ^ 40 * 3994593 * 2
def baseEnd_3994593 : Nat := 2051146228085594870216707

theorem tailTrace_3994593 : CollatzResearch.WordTrace tailWord_3994593 prefixEnd_3994593 2051146228085594870216707 := by
  unfold tailWord_3994593
  simp only [CollatzResearch.WordTrace]
  refine ⟨145694776017279258015028433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97129850678186172010018955 145694776017279258015028433)
  ·
    refine ⟨109271082012959443511271325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145694776017279258015028433 109271082012959443511271325)
    ·
      refine ⟨40976655754859791316726747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109271082012959443511271325 40976655754859791316726747)
      ·
        refine ⟨61464983632289686975090121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40976655754859791316726747 61464983632289686975090121)
        ·
          refine ⟨46098737724217265231317591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61464983632289686975090121 46098737724217265231317591)
          ·
            refine ⟨69148106586325897846976387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46098737724217265231317591 69148106586325897846976387)
            ·
              refine ⟨103722159879488846770464581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69148106586325897846976387 103722159879488846770464581)
              ·
                refine ⟨19447904977404158769462109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103722159879488846770464581 19447904977404158769462109)
                ·
                  refine ⟨7292964366526559538548291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19447904977404158769462109 7292964366526559538548291)
                  ·
                    refine ⟨10939446549789839307822437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7292964366526559538548291 10939446549789839307822437)
                    ·
                      refine ⟨2051146228085594870216707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10939446549789839307822437 2051146228085594870216707)
                      ·
                        rfl

theorem cell23_3994593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3994593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994593 prefixEnd_3994593 := by exact prefixLift 3994593
  have htrace : WordTrace (prefixWord ++ tailWord_3994593) baseStart_3994593 baseEnd_3994593 := by
    simpa [prefixWord, tailWord_3994593, baseEnd_3994593] using wordTrace_append hprefix tailTrace_3994593
  have hstable : (prefixWord ++ tailWord_3994593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994593).length < 2 ^ (prefixWord ++ tailWord_3994593).sum := by decide
  have hdescent : baseEnd_3994593 < baseStart_3994593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994594 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3994594 : Nat := 118140960795 + 3994594 * 2 ^ 59
def prefixEnd_3994594 : Nat := 4983230072969 + 3 ^ 40 * 3994594 * 2
def baseEnd_3994594 : Nat := 227905193507361040700467

theorem tailTrace_3994594 : CollatzResearch.WordTrace tailWord_3994594 prefixEnd_3994594 227905193507361040700467 := by
  unfold tailWord_3994594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36423703122568908796453709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97129874993517090123876557 36423703122568908796453709)
  ·
    refine ⟨13658888670963340798670141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36423703122568908796453709 13658888670963340798670141)
    ·
      refine ⟨5122083251611252799501303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13658888670963340798670141 5122083251611252799501303)
      ·
        refine ⟨7683124877416879199251955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122083251611252799501303 7683124877416879199251955)
        ·
          refine ⟨11524687316125318798877933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683124877416879199251955 11524687316125318798877933)
          ·
            refine ⟨4321757743546994549579225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11524687316125318798877933 4321757743546994549579225)
            ·
              refine ⟨3241318307660245912184419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4321757743546994549579225 3241318307660245912184419)
              ·
                refine ⟨4861977461490368868276629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3241318307660245912184419 4861977461490368868276629)
                ·
                  refine ⟨227905193507361040700467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4861977461490368868276629 227905193507361040700467)
                  ·
                    rfl

theorem cell23_3994594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3994594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994594 prefixEnd_3994594 := by exact prefixLift 3994594
  have htrace : WordTrace (prefixWord ++ tailWord_3994594) baseStart_3994594 baseEnd_3994594 := by
    simpa [prefixWord, tailWord_3994594, baseEnd_3994594] using wordTrace_append hprefix tailTrace_3994594
  have hstable : (prefixWord ++ tailWord_3994594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994594).length < 2 ^ (prefixWord ++ tailWord_3994594).sum := by decide
  have hdescent : baseEnd_3994594 < baseStart_3994594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994614 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_3994614 : Nat := 118140960795 + 3994614 * 2 ^ 59
def prefixEnd_3994614 : Nat := 4983230072969 + 3 ^ 40 * 3994614 * 2
def baseEnd_3994614 : Nat := 2051157011179339288054111

theorem tailTrace_3994614 : CollatzResearch.WordTrace tailWord_3994614 prefixEnd_3994614 2051157011179339288054111 := by
  unfold tailWord_3994614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105971371887698662596431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97130361300135452401028597 9105971371887698662596431)
  ·
    refine ⟨13658957057831547993894647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9105971371887698662596431 13658957057831547993894647)
    ·
      refine ⟨20488435586747321990841971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13658957057831547993894647 20488435586747321990841971)
      ·
        refine ⟨30732653380120982986262957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20488435586747321990841971 30732653380120982986262957)
        ·
          refine ⟨11524745017545368619848609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30732653380120982986262957 11524745017545368619848609)
          ·
            refine ⟨8643558763159026464886457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11524745017545368619848609 8643558763159026464886457)
            ·
              refine ⟨6482669072369269848664843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8643558763159026464886457 6482669072369269848664843)
              ·
                refine ⟨9724003608553904772997265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482669072369269848664843 9724003608553904772997265)
                ·
                  refine ⟨7293002706415428579747949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9724003608553904772997265 7293002706415428579747949)
                  ·
                    refine ⟨2734876014905785717405481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7293002706415428579747949 2734876014905785717405481)
                    ·
                      refine ⟨2051157011179339288054111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734876014905785717405481 2051157011179339288054111)
                      ·
                        rfl

theorem cell23_3994614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_3994614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994614 prefixEnd_3994614 := by exact prefixLift 3994614
  have htrace : WordTrace (prefixWord ++ tailWord_3994614) baseStart_3994614 baseEnd_3994614 := by
    simpa [prefixWord, tailWord_3994614, baseEnd_3994614] using wordTrace_append hprefix tailTrace_3994614
  have hstable : (prefixWord ++ tailWord_3994614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994614).length < 2 ^ (prefixWord ++ tailWord_3994614).sum := by decide
  have hdescent : baseEnd_3994614 < baseStart_3994614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994643 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3]
def baseStart_3994643 : Nat := 118140960795 + 3994643 * 2 ^ 59
def prefixEnd_3994643 : Nat := 4983230072969 + 3 ^ 40 * 3994643 * 2
def baseEnd_3994643 : Nat := 2051171902118319674591477

theorem tailTrace_3994643 : CollatzResearch.WordTrace tailWord_3994643 prefixEnd_3994643 2051171902118319674591477 := by
  unfold tailWord_3994643
  simp only [CollatzResearch.WordTrace]
  refine ⟨145696599667098116554348583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97131066444732077702899055 145696599667098116554348583)
  ·
    refine ⟨218544899500647174831522875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145696599667098116554348583 218544899500647174831522875)
    ·
      refine ⟨327817349250970762247284313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218544899500647174831522875 327817349250970762247284313)
      ·
        refine ⟨245863011938228071685463235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327817349250970762247284313 245863011938228071685463235)
        ·
          refine ⟨368794517907342107528194853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245863011938228071685463235 368794517907342107528194853)
          ·
            refine ⟨69148972107626645161536535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 368794517907342107528194853 69148972107626645161536535)
            ·
              refine ⟨103723458161439967742304803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69148972107626645161536535 103723458161439967742304803)
              ·
                refine ⟨155585187242159951613457205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103723458161439967742304803 155585187242159951613457205)
                ·
                  refine ⟨14586111303952495463761613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 155585187242159951613457205 14586111303952495463761613)
                  ·
                    refine ⟨5469791738982185798910605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14586111303952495463761613 5469791738982185798910605)
                    ·
                      refine ⟨2051171902118319674591477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5469791738982185798910605 2051171902118319674591477)
                      ·
                        rfl

theorem cell23_3994643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_3994643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994643 prefixEnd_3994643 := by exact prefixLift 3994643
  have htrace : WordTrace (prefixWord ++ tailWord_3994643) baseStart_3994643 baseEnd_3994643 := by
    simpa [prefixWord, tailWord_3994643, baseEnd_3994643] using wordTrace_append hprefix tailTrace_3994643
  have hstable : (prefixWord ++ tailWord_3994643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994643).length < 2 ^ (prefixWord ++ tailWord_3994643).sum := by decide
  have hdescent : baseEnd_3994643 < baseStart_3994643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994673 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3994673 : Nat := 118140960795 + 3994673 * 2 ^ 59
def prefixEnd_3994673 : Nat := 4983230072969 + 3 ^ 40 * 3994673 * 2
def baseEnd_3994673 : Nat := 2051187306537954557216339

theorem tailTrace_3994673 : CollatzResearch.WordTrace tailWord_3994673 prefixEnd_3994673 2051187306537954557216339 := by
  unfold tailWord_3994673
  simp only [CollatzResearch.WordTrace]
  refine ⟨145697693856989431677940673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97131795904659621118627115 145697693856989431677940673)
  ·
    refine ⟨109273270392742073758455505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145697693856989431677940673 109273270392742073758455505)
    ·
      refine ⟨81954952794556555318841629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109273270392742073758455505 81954952794556555318841629)
      ·
        refine ⟨30733107297958708244565611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81954952794556555318841629 30733107297958708244565611)
        ·
          refine ⟨46099660946938062366848417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30733107297958708244565611 46099660946938062366848417)
          ·
            refine ⟨34574745710203546775136313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46099660946938062366848417 34574745710203546775136313)
            ·
              refine ⟨25931059282652660081352235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34574745710203546775136313 25931059282652660081352235)
              ·
                refine ⟨38896588923978990122028353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25931059282652660081352235 38896588923978990122028353)
                ·
                  refine ⟨29172441692984242591521265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38896588923978990122028353 29172441692984242591521265)
                  ·
                    refine ⟨21879331269738181943640949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29172441692984242591521265 21879331269738181943640949)
                    ·
                      refine ⟨2051187306537954557216339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21879331269738181943640949 2051187306537954557216339)
                      ·
                        rfl

theorem cell23_3994673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3994673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994673 prefixEnd_3994673 := by exact prefixLift 3994673
  have htrace : WordTrace (prefixWord ++ tailWord_3994673) baseStart_3994673 baseEnd_3994673 := by
    simpa [prefixWord, tailWord_3994673, baseEnd_3994673] using wordTrace_append hprefix tailTrace_3994673
  have hstable : (prefixWord ++ tailWord_3994673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994673).length < 2 ^ (prefixWord ++ tailWord_3994673).sum := by decide
  have hdescent : baseEnd_3994673 < baseStart_3994673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994678 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_3994678 : Nat := 118140960795 + 3994678 * 2 ^ 59
def prefixEnd_3994678 : Nat := 4983230072969 + 3 ^ 40 * 3994678 * 2
def baseEnd_3994678 : Nat := 2051189873941227037653817

theorem tailTrace_3994678 : CollatzResearch.WordTrace tailWord_3994678 prefixEnd_3994678 2051189873941227037653817 := by
  unfold tailWord_3994678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106117263873207345742043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97131917481314211687915125 9106117263873207345742043)
  ·
    refine ⟨13659175895809811018613065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9106117263873207345742043 13659175895809811018613065)
    ·
      refine ⟨10244381921857358263959799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13659175895809811018613065 10244381921857358263959799)
      ·
        refine ⟨15366572882786037395939699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10244381921857358263959799 15366572882786037395939699)
        ·
          refine ⟨23049859324179056093909549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15366572882786037395939699 23049859324179056093909549)
          ·
            refine ⟨8643697246567146035216081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23049859324179056093909549 8643697246567146035216081)
            ·
              refine ⟨6482772934925359526412061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8643697246567146035216081 6482772934925359526412061)
              ·
                refine ⟨2431039850597009822404523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6482772934925359526412061 2431039850597009822404523)
                ·
                  refine ⟨3646559775895514733606785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431039850597009822404523 3646559775895514733606785)
                  ·
                    refine ⟨2734919831921636050205089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3646559775895514733606785 2734919831921636050205089)
                    ·
                      refine ⟨2051189873941227037653817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734919831921636050205089 2051189873941227037653817)
                      ·
                        rfl

theorem cell23_3994678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_3994678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994678 prefixEnd_3994678 := by exact prefixLift 3994678
  have htrace : WordTrace (prefixWord ++ tailWord_3994678) baseStart_3994678 baseEnd_3994678 := by
    simpa [prefixWord, tailWord_3994678, baseEnd_3994678] using wordTrace_append hprefix tailTrace_3994678
  have hstable : (prefixWord ++ tailWord_3994678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994678).length < 2 ^ (prefixWord ++ tailWord_3994678).sum := by decide
  have hdescent : baseEnd_3994678 < baseStart_3994678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994693 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_3994693 : Nat := 118140960795 + 3994693 * 2 ^ 59
def prefixEnd_3994693 : Nat := 4983230072969 + 3 ^ 40 * 3994693 * 2
def baseEnd_3994693 : Nat := 683732525383681492988749

theorem tailTrace_3994693 : CollatzResearch.WordTrace tailWord_3994693 prefixEnd_3994693 683732525383681492988749 := by
  unfold tailWord_3994693
  simp only [CollatzResearch.WordTrace]
  refine ⟨145698423316916975093668733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97132282211277983395779155 145698423316916975093668733)
  ·
    refine ⟨54636908743843865660125775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145698423316916975093668733 54636908743843865660125775)
    ·
      refine ⟨81955363115765798490188663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54636908743843865660125775 81955363115765798490188663)
      ·
        refine ⟨122933044673648697735282995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81955363115765798490188663 122933044673648697735282995)
        ·
          refine ⟨184399567010473046602924493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122933044673648697735282995 184399567010473046602924493)
          ·
            refine ⟨69149837628927392476096685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184399567010473046602924493 69149837628927392476096685)
            ·
              refine ⟨25931189110847772178536257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69149837628927392476096685 25931189110847772178536257)
              ·
                refine ⟨19448391833135829133902193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25931189110847772178536257 19448391833135829133902193)
                ·
                  refine ⟨14586293874851871850426645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19448391833135829133902193 14586293874851871850426645)
                  ·
                    refine ⟨683732525383681492988749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14586293874851871850426645 683732525383681492988749)
                    ·
                      rfl

theorem cell23_3994693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_3994693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994693 prefixEnd_3994693 := by exact prefixLift 3994693
  have htrace : WordTrace (prefixWord ++ tailWord_3994693) baseStart_3994693 baseEnd_3994693 := by
    simpa [prefixWord, tailWord_3994693, baseEnd_3994693] using wordTrace_append hprefix tailTrace_3994693
  have hstable : (prefixWord ++ tailWord_3994693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994693).length < 2 ^ (prefixWord ++ tailWord_3994693).sum := by decide
  have hdescent : baseEnd_3994693 < baseStart_3994693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994713 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_3994713 : Nat := 118140960795 + 3994713 * 2 ^ 59
def prefixEnd_3994713 : Nat := 4983230072969 + 3 ^ 40 * 3994713 * 2
def baseEnd_3994713 : Nat := 2051207845764134400716155

theorem tailTrace_3994713 : CollatzResearch.WordTrace tailWord_3994713 prefixEnd_3994713 2051207845764134400716155 := by
  unfold tailWord_3994713
  simp only [CollatzResearch.WordTrace]
  refine ⟨145699152776844518509396793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97132768517896345672931195 145699152776844518509396793)
  ·
    refine ⟨109274364582633388882047595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145699152776844518509396793 109274364582633388882047595)
    ·
      refine ⟨163911546873950083323071393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109274364582633388882047595 163911546873950083323071393)
      ·
        refine ⟨122933660155462562492303545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163911546873950083323071393 122933660155462562492303545)
        ·
          refine ⟨92200245116596921869227659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122933660155462562492303545 92200245116596921869227659)
          ·
            refine ⟨138300367674895382803841489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92200245116596921869227659 138300367674895382803841489)
            ·
              refine ⟨103725275756171537102881117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138300367674895382803841489 103725275756171537102881117)
              ·
                refine ⟨38896978408564326413580419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103725275756171537102881117 38896978408564326413580419)
                ·
                  refine ⟨58345467612846489620370629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38896978408564326413580419 58345467612846489620370629)
                  ·
                    refine ⟨10939775177408716803819493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58345467612846489620370629 10939775177408716803819493)
                    ·
                      refine ⟨2051207845764134400716155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10939775177408716803819493 2051207845764134400716155)
                      ·
                        rfl

theorem cell23_3994713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_3994713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994713 prefixEnd_3994713 := by exact prefixLift 3994713
  have htrace : WordTrace (prefixWord ++ tailWord_3994713) baseStart_3994713 baseEnd_3994713 := by
    simpa [prefixWord, tailWord_3994713, baseEnd_3994713] using wordTrace_append hprefix tailTrace_3994713
  have hstable : (prefixWord ++ tailWord_3994713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994713).length < 2 ^ (prefixWord ++ tailWord_3994713).sum := by decide
  have hdescent : baseEnd_3994713 < baseStart_3994713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994734 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3994734 : Nat := 118140960795 + 3994734 * 2 ^ 59
def prefixEnd_3994734 : Nat := 4983230072969 + 3 ^ 40 * 3994734 * 2
def baseEnd_3994734 : Nat := 2051218628857878818553559

theorem tailTrace_3994734 : CollatzResearch.WordTrace tailWord_3994734 prefixEnd_3994734 2051218628857878818553559 := by
  unfold tailWord_3994734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18212489838721054886988907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97133279139845626063940837 18212489838721054886988907)
  ·
    refine ⟨27318734758081582330483361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18212489838721054886988907 27318734758081582330483361)
    ·
      refine ⟨20489051068561186747862521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27318734758081582330483361 20489051068561186747862521)
      ·
        refine ⟨15366788301420890060896891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20489051068561186747862521 15366788301420890060896891)
        ·
          refine ⟨23050182452131335091345337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15366788301420890060896891 23050182452131335091345337)
          ·
            refine ⟨17287636839098501318509003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23050182452131335091345337 17287636839098501318509003)
            ·
              refine ⟨25931455258647751977763505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17287636839098501318509003 25931455258647751977763505)
              ·
                refine ⟨19448591443985813983322629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25931455258647751977763505 19448591443985813983322629)
                ·
                  refine ⟨3646610895747340121872993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19448591443985813983322629 3646610895747340121872993)
                  ·
                    refine ⟨2734958171810505091404745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3646610895747340121872993 2734958171810505091404745)
                    ·
                      refine ⟨2051218628857878818553559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2734958171810505091404745 2051218628857878818553559)
                      ·
                        rfl

theorem cell23_3994734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3994734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994734 prefixEnd_3994734 := by exact prefixLift 3994734
  have htrace : WordTrace (prefixWord ++ tailWord_3994734) baseStart_3994734 baseEnd_3994734 := by
    simpa [prefixWord, tailWord_3994734, baseEnd_3994734] using wordTrace_append hprefix tailTrace_3994734
  have hstable : (prefixWord ++ tailWord_3994734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994734).length < 2 ^ (prefixWord ++ tailWord_3994734).sum := by decide
  have hdescent : baseEnd_3994734 < baseStart_3994734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994757 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 7]
def baseStart_3994757 : Nat := 118140960795 + 3994757 * 2 ^ 59
def prefixEnd_3994757 : Nat := 4983230072969 + 3 ^ 40 * 3994757 * 2
def baseEnd_3994757 : Nat := 227914493212548025396217

theorem tailTrace_3994757 : CollatzResearch.WordTrace tailWord_3994757 prefixEnd_3994757 227914493212548025396217 := by
  unfold tailWord_3994757
  simp only [CollatzResearch.WordTrace]
  refine ⟨145700757588685114023998525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97133838392456742682665683 145700757588685114023998525)
  ·
    refine ⟨54637784095756917758999447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145700757588685114023998525 54637784095756917758999447)
    ·
      refine ⟨81956676143635376638499171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54637784095756917758999447 81956676143635376638499171)
      ·
        refine ⟨122935014215453064957748757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81956676143635376638499171 122935014215453064957748757)
        ·
          refine ⟨5762578791349362419894473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122935014215453064957748757 5762578791349362419894473)
          ·
            refine ⟨4321934093512021814920855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5762578791349362419894473 4321934093512021814920855)
            ·
              refine ⟨6482901140268032722381283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4321934093512021814920855 6482901140268032722381283)
              ·
                refine ⟨9724351710402049083571925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482901140268032722381283 9724351710402049083571925)
                ·
                  refine ⟨227914493212548025396217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9724351710402049083571925 227914493212548025396217)
                  ·
                    rfl

theorem cell23_3994757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_3994757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994757 prefixEnd_3994757 := by exact prefixLift 3994757
  have htrace : WordTrace (prefixWord ++ tailWord_3994757) baseStart_3994757 baseEnd_3994757 := by
    simpa [prefixWord, tailWord_3994757, baseEnd_3994757] using wordTrace_append hprefix tailTrace_3994757
  have hstable : (prefixWord ++ tailWord_3994757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994757).length < 2 ^ (prefixWord ++ tailWord_3994757).sum := by decide
  have hdescent : baseEnd_3994757 < baseStart_3994757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994800 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_3994800 : Nat := 118140960795 + 3994800 * 2 ^ 59
def prefixEnd_3994800 : Nat := 4983230072969 + 3 ^ 40 * 3994800 * 2
def baseEnd_3994800 : Nat := 683750839527025186776085

theorem tailTrace_3994800 : CollatzResearch.WordTrace tailWord_3994800 prefixEnd_3994800 683750839527025186776085 := by
  unfold tailWord_3994800
  simp only [CollatzResearch.WordTrace]
  refine ⟨72851162963764666183906927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97134883951686221578542569 72851162963764666183906927)
  ·
    refine ⟨109276744445646999275860391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72851162963764666183906927 109276744445646999275860391)
    ·
      refine ⟨163915116668470498913790587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109276744445646999275860391 163915116668470498913790587)
      ·
        refine ⟨245872675002705748370685881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163915116668470498913790587 245872675002705748370685881)
        ·
          refine ⟨184404506252029311278014411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245872675002705748370685881 184404506252029311278014411)
          ·
            refine ⟨276606759378043966917021617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184404506252029311278014411 276606759378043966917021617)
            ·
              refine ⟨207455069533532975187766213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276606759378043966917021617 207455069533532975187766213)
              ·
                refine ⟨38897825537537432847706165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207455069533532975187766213 38897825537537432847706165)
                ·
                  refine ⟨3646671144144134329472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38897825537537432847706165 3646671144144134329472453)
                  ·
                    refine ⟨683750839527025186776085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646671144144134329472453 683750839527025186776085)
                    ·
                      rfl

theorem cell23_3994800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_3994800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994800 prefixEnd_3994800 := by exact prefixLift 3994800
  have htrace : WordTrace (prefixWord ++ tailWord_3994800) baseStart_3994800 baseEnd_3994800 := by
    simpa [prefixWord, tailWord_3994800, baseEnd_3994800] using wordTrace_append hprefix tailTrace_3994800
  have hstable : (prefixWord ++ tailWord_3994800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994800).length < 2 ^ (prefixWord ++ tailWord_3994800).sum := by decide
  have hdescent : baseEnd_3994800 < baseStart_3994800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994807 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_3994807 : Nat := 118140960795 + 3994807 * 2 ^ 59
def prefixEnd_3994807 : Nat := 4983230072969 + 3 ^ 40 * 3994807 * 2
def baseEnd_3994807 : Nat := 2051256112945657032940723

theorem tailTrace_3994807 : CollatzResearch.WordTrace tailWord_3994807 prefixEnd_3994807 2051256112945657032940723 := by
  unfold tailWord_3994807
  simp only [CollatzResearch.WordTrace]
  refine ⟨145702581238503972563318675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97135054159002648375545783 145702581238503972563318675)
  ·
    refine ⟨218553871857755958844978013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145702581238503972563318675 218553871857755958844978013)
    ·
      refine ⟨81957701946658484566866755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218553871857755958844978013 81957701946658484566866755)
      ·
        refine ⟨122936552919987726850300133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81957701946658484566866755 122936552919987726850300133)
        ·
          refine ⟨23050603672497698784431275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122936552919987726850300133 23050603672497698784431275)
          ·
            refine ⟨34575905508746548176646913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23050603672497698784431275 34575905508746548176646913)
            ·
              refine ⟨25931929131559911132485185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34575905508746548176646913 25931929131559911132485185)
              ·
                refine ⟨19448946848669933349363889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25931929131559911132485185 19448946848669933349363889)
                ·
                  refine ⟨14586710136502450012022917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19448946848669933349363889 14586710136502450012022917)
                  ·
                    refine ⟨2735008150594209377254297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14586710136502450012022917 2735008150594209377254297)
                    ·
                      refine ⟨2051256112945657032940723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735008150594209377254297 2051256112945657032940723)
                      ·
                        rfl

theorem cell23_3994807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_3994807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994807 prefixEnd_3994807 := by exact prefixLift 3994807
  have htrace : WordTrace (prefixWord ++ tailWord_3994807) baseStart_3994807 baseEnd_3994807 := by
    simpa [prefixWord, tailWord_3994807, baseEnd_3994807] using wordTrace_append hprefix tailTrace_3994807
  have hstable : (prefixWord ++ tailWord_3994807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994807).length < 2 ^ (prefixWord ++ tailWord_3994807).sum := by decide
  have hdescent : baseEnd_3994807 < baseStart_3994807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994810 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_3994810 : Nat := 118140960795 + 3994810 * 2 ^ 59
def prefixEnd_3994810 : Nat := 4983230072969 + 3 ^ 40 * 3994810 * 2
def baseEnd_3994810 : Nat := 2051257653387620521203209

theorem tailTrace_3994810 : CollatzResearch.WordTrace tailWord_3994810 prefixEnd_3994810 2051257653387620521203209 := by
  unfold tailWord_3994810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36425672664373276018919471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97135127104995402717118589 36425672664373276018919471)
  ·
    refine ⟨54638508996559914028379207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36425672664373276018919471 54638508996559914028379207)
    ·
      refine ⟨81957763494839871042568811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54638508996559914028379207 81957763494839871042568811)
      ·
        refine ⟨122936645242259806563853217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81957763494839871042568811 122936645242259806563853217)
        ·
          refine ⟨92202483931694854922889913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122936645242259806563853217 92202483931694854922889913)
          ·
            refine ⟨69151862948771141192167435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92202483931694854922889913 69151862948771141192167435)
            ·
              refine ⟨103727794423156711788251153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69151862948771141192167435 103727794423156711788251153)
              ·
                refine ⟨77795845817367533841188365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103727794423156711788251153 77795845817367533841188365)
                ·
                  refine ⟨29173442181512825190445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77795845817367533841188365 29173442181512825190445637)
                  ·
                    refine ⟨5470020409033654723208557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29173442181512825190445637 5470020409033654723208557)
                    ·
                      refine ⟨2051257653387620521203209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470020409033654723208557 2051257653387620521203209)
                      ·
                        rfl

theorem cell23_3994810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_3994810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994810 prefixEnd_3994810 := by exact prefixLift 3994810
  have htrace : WordTrace (prefixWord ++ tailWord_3994810) baseStart_3994810 baseEnd_3994810 := by
    simpa [prefixWord, tailWord_3994810, baseEnd_3994810] using wordTrace_append hprefix tailTrace_3994810
  have hstable : (prefixWord ++ tailWord_3994810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994810).length < 2 ^ (prefixWord ++ tailWord_3994810).sum := by decide
  have hdescent : baseEnd_3994810 < baseStart_3994810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994838 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3994838 : Nat := 118140960795 + 3994838 * 2 ^ 59
def prefixEnd_3994838 : Nat := 4983230072969 + 3 ^ 40 * 3994838 * 2
def baseEnd_3994838 : Nat := 683757343615315470551027

theorem tailTrace_3994838 : CollatzResearch.WordTrace tailWord_3994838 prefixEnd_3994838 683757343615315470551027 := by
  unfold tailWord_3994838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106481993836979053606073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97135807934261109905131445 9106481993836979053606073)
  ·
    refine ⟨6829861495377734290204555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9106481993836979053606073 6829861495377734290204555)
    ·
      refine ⟨10244792243066601435306833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829861495377734290204555 10244792243066601435306833)
      ·
        refine ⟨7683594182299951076480125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10244792243066601435306833 7683594182299951076480125)
        ·
          refine ⟨2881347818362481653680047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7683594182299951076480125 2881347818362481653680047)
          ·
            refine ⟨4322021727543722480520071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881347818362481653680047 4322021727543722480520071)
            ·
              refine ⟨6483032591315583720780107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322021727543722480520071 6483032591315583720780107)
              ·
                refine ⟨9724548886973375581170161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483032591315583720780107 9724548886973375581170161)
                ·
                  refine ⟨7293411665230031685877621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9724548886973375581170161 7293411665230031685877621)
                  ·
                    refine ⟨683757343615315470551027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7293411665230031685877621 683757343615315470551027)
                    ·
                      rfl

theorem cell23_3994838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3994838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994838 prefixEnd_3994838 := by exact prefixLift 3994838
  have htrace : WordTrace (prefixWord ++ tailWord_3994838) baseStart_3994838 baseEnd_3994838 := by
    simpa [prefixWord, tailWord_3994838, baseEnd_3994838] using wordTrace_append hprefix tailTrace_3994838
  have hstable : (prefixWord ++ tailWord_3994838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994838).length < 2 ^ (prefixWord ++ tailWord_3994838).sum := by decide
  have hdescent : baseEnd_3994838 < baseStart_3994838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994874 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_3994874 : Nat := 118140960795 + 3994874 * 2 ^ 59
def prefixEnd_3994874 : Nat := 4983230072969 + 3 ^ 40 * 3994874 * 2
def baseEnd_3994874 : Nat := 2051290516149508270802915

theorem tailTrace_3994874 : CollatzResearch.WordTrace tailWord_3994874 prefixEnd_3994874 2051290516149508270802915 := by
  unfold tailWord_3994874
  simp only [CollatzResearch.WordTrace]
  refine ⟨36426256232315310751501919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97136683286174162004005117 36426256232315310751501919)
  ·
    refine ⟨54639384348472966127252879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36426256232315310751501919 54639384348472966127252879)
    ·
      refine ⟨81959076522709449190879319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54639384348472966127252879 81959076522709449190879319)
      ·
        refine ⟨122938614784064173786318979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81959076522709449190879319 122938614784064173786318979)
        ·
          refine ⟨184407922176096260679478469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122938614784064173786318979 184407922176096260679478469)
          ·
            refine ⟨34576485408018048877402213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184407922176096260679478469 34576485408018048877402213)
            ·
              refine ⟨6483091014003384164512915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34576485408018048877402213 6483091014003384164512915)
              ·
                refine ⟨9724636521005076246769373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483091014003384164512915 9724636521005076246769373)
                ·
                  refine ⟨3646738695376903592538515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9724636521005076246769373 3646738695376903592538515)
                  ·
                    refine ⟨5470108043065355388807773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646738695376903592538515 5470108043065355388807773)
                    ·
                      refine ⟨2051290516149508270802915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470108043065355388807773 2051290516149508270802915)
                      ·
                        rfl

theorem cell23_3994874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_3994874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994874 prefixEnd_3994874 := by exact prefixLift 3994874
  have htrace : WordTrace (prefixWord ++ tailWord_3994874) baseStart_3994874 baseEnd_3994874 := by
    simpa [prefixWord, tailWord_3994874, baseEnd_3994874] using wordTrace_append hprefix tailTrace_3994874
  have hstable : (prefixWord ++ tailWord_3994874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994874).length < 2 ^ (prefixWord ++ tailWord_3994874).sum := by decide
  have hdescent : baseEnd_3994874 < baseStart_3994874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994884 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3994884 : Nat := 118140960795 + 3994884 * 2 ^ 59
def prefixEnd_3994884 : Nat := 4983230072969 + 3 ^ 40 * 3994884 * 2
def baseEnd_3994884 : Nat := 2051295650956053231677869

theorem tailTrace_3994884 : CollatzResearch.WordTrace tailWord_3994884 prefixEnd_3994884 2051295650956053231677869 := by
  unfold tailWord_3994884
  simp only [CollatzResearch.WordTrace]
  refine ⟨72852694829612507356935853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97136926439483343142581137 72852694829612507356935853)
  ·
    refine ⟨27319760561104690258850945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72852694829612507356935853 27319760561104690258850945)
    ·
      refine ⟨20489820420828517694138209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27319760561104690258850945 20489820420828517694138209)
      ·
        refine ⟨15367365315621388270603657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20489820420828517694138209 15367365315621388270603657)
        ·
          refine ⟨11525523986716041202952743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15367365315621388270603657 11525523986716041202952743)
          ·
            refine ⟨17288285980074061804429115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525523986716041202952743 17288285980074061804429115)
            ·
              refine ⟨25932428970111092706643673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17288285980074061804429115 25932428970111092706643673)
              ·
                refine ⟨19449321727583319529982755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25932428970111092706643673 19449321727583319529982755)
                ·
                  refine ⟨29173982591374979294974133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19449321727583319529982755 29173982591374979294974133)
                  ·
                    refine ⟨2735060867941404308903825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29173982591374979294974133 2735060867941404308903825)
                    ·
                      refine ⟨2051295650956053231677869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735060867941404308903825 2051295650956053231677869)
                      ·
                        rfl

theorem cell23_3994884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3994884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994884 prefixEnd_3994884 := by exact prefixLift 3994884
  have htrace : WordTrace (prefixWord ++ tailWord_3994884) baseStart_3994884 baseEnd_3994884 := by
    simpa [prefixWord, tailWord_3994884, baseEnd_3994884] using wordTrace_append hprefix tailTrace_3994884
  have hstable : (prefixWord ++ tailWord_3994884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994884).length < 2 ^ (prefixWord ++ tailWord_3994884).sum := by decide
  have hdescent : baseEnd_3994884 < baseStart_3994884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994894 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3994894 : Nat := 118140960795 + 3994894 * 2 ^ 59
def prefixEnd_3994894 : Nat := 4983230072969 + 3 ^ 40 * 3994894 * 2
def baseEnd_3994894 : Nat := 683766928587532730850941

theorem tailTrace_3994894 : CollatzResearch.WordTrace tailWord_3994894 prefixEnd_3994894 683766928587532730850941 := by
  unfold tailWord_3994894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213219298648598302716967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97137169592792524281157157 18213219298648598302716967)
  ·
    refine ⟨27319828947972897454075451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18213219298648598302716967 27319828947972897454075451)
    ·
      refine ⟨40979743421959346181113177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27319828947972897454075451 40979743421959346181113177)
      ·
        refine ⟨30734807566469509635834883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40979743421959346181113177 30734807566469509635834883)
        ·
          refine ⟨46102211349704264453752325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30734807566469509635834883 46102211349704264453752325)
          ·
            refine ⟨8644164628069549585078561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46102211349704264453752325 8644164628069549585078561)
            ·
              refine ⟨6483123471052162188808921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8644164628069549585078561 6483123471052162188808921)
              ·
                refine ⟨4862342603289121641606691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483123471052162188808921 4862342603289121641606691)
                ·
                  refine ⟨7293513904933682462410037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862342603289121641606691 7293513904933682462410037)
                  ·
                    refine ⟨683766928587532730850941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7293513904933682462410037 683766928587532730850941)
                    ·
                      rfl

theorem cell23_3994894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3994894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994894 prefixEnd_3994894 := by exact prefixLift 3994894
  have htrace : WordTrace (prefixWord ++ tailWord_3994894) baseStart_3994894 baseEnd_3994894 := by
    simpa [prefixWord, tailWord_3994894, baseEnd_3994894] using wordTrace_append hprefix tailTrace_3994894
  have hstable : (prefixWord ++ tailWord_3994894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994894).length < 2 ^ (prefixWord ++ tailWord_3994894).sum := by decide
  have hdescent : baseEnd_3994894 < baseStart_3994894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994897 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_3994897 : Nat := 118140960795 + 3994897 * 2 ^ 59
def prefixEnd_3994897 : Nat := 4983230072969 + 3 ^ 40 * 3994897 * 2
def baseEnd_3994897 : Nat := 2051302326204561680815309

theorem tailTrace_3994897 : CollatzResearch.WordTrace tailWord_3994897 prefixEnd_3994897 2051302326204561680815309 := by
  unfold tailWord_3994897
  simp only [CollatzResearch.WordTrace]
  refine ⟨145705863808177917934094945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97137242538785278622729963 145705863808177917934094945)
  ·
    refine ⟨109279397856133438450571209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145705863808177917934094945 109279397856133438450571209)
    ·
      refine ⟨81959548392100078837928407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109279397856133438450571209 81959548392100078837928407)
      ·
        refine ⟨122939322588150118256892611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81959548392100078837928407 122939322588150118256892611)
        ·
          refine ⟨184408983882225177385338917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122939322588150118256892611 184408983882225177385338917)
          ·
            refine ⟨34576684477917220759751047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184408983882225177385338917 34576684477917220759751047)
            ·
              refine ⟨51865026716875831139626571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34576684477917220759751047 51865026716875831139626571)
              ·
                refine ⟨77797540075313746709439857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51865026716875831139626571 77797540075313746709439857)
                ·
                  refine ⟨58348155056485310032079893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77797540075313746709439857 58348155056485310032079893)
                  ·
                    refine ⟨2735069768272748907753745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58348155056485310032079893 2735069768272748907753745)
                    ·
                      refine ⟨2051302326204561680815309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735069768272748907753745 2051302326204561680815309)
                      ·
                        rfl

theorem cell23_3994897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_3994897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994897 prefixEnd_3994897 := by exact prefixLift 3994897
  have htrace : WordTrace (prefixWord ++ tailWord_3994897) baseStart_3994897 baseEnd_3994897 := by
    simpa [prefixWord, tailWord_3994897, baseEnd_3994897] using wordTrace_append hprefix tailTrace_3994897
  have hstable : (prefixWord ++ tailWord_3994897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994897).length < 2 ^ (prefixWord ++ tailWord_3994897).sum := by decide
  have hdescent : baseEnd_3994897 < baseStart_3994897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994917 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3994917 : Nat := 118140960795 + 3994917 * 2 ^ 59
def prefixEnd_3994917 : Nat := 4983230072969 + 3 ^ 40 * 3994917 * 2
def baseEnd_3994917 : Nat := 2051312595817651602565217

theorem tailTrace_3994917 : CollatzResearch.WordTrace tailWord_3994917 prefixEnd_3994917 2051312595817651602565217 := by
  unfold tailWord_3994917
  simp only [CollatzResearch.WordTrace]
  refine ⟨145706593268105461349823005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97137728845403640899882003 145706593268105461349823005)
  ·
    refine ⟨54639972475539548006183627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145706593268105461349823005 54639972475539548006183627)
    ·
      refine ⟨81959958713309322009275441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54639972475539548006183627 81959958713309322009275441)
      ·
        refine ⟨61469969034981991506956581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81959958713309322009275441 61469969034981991506956581)
        ·
          refine ⟨11525619194059123407554359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61469969034981991506956581 11525619194059123407554359)
          ·
            refine ⟨17288428791088685111331539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525619194059123407554359 17288428791088685111331539)
            ·
              refine ⟨25932643186633027666997309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17288428791088685111331539 25932643186633027666997309)
              ·
                refine ⟨9724741194987385375123991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25932643186633027666997309 9724741194987385375123991)
                ·
                  refine ⟨14587111792481078062685987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724741194987385375123991 14587111792481078062685987)
                  ·
                    refine ⟨21880667688721617094028981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14587111792481078062685987 21880667688721617094028981)
                    ·
                      refine ⟨2051312595817651602565217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21880667688721617094028981 2051312595817651602565217)
                      ·
                        rfl

theorem cell23_3994917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3994917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994917 prefixEnd_3994917 := by exact prefixLift 3994917
  have htrace : WordTrace (prefixWord ++ tailWord_3994917) baseStart_3994917 baseEnd_3994917 := by
    simpa [prefixWord, tailWord_3994917, baseEnd_3994917] using wordTrace_append hprefix tailTrace_3994917
  have hstable : (prefixWord ++ tailWord_3994917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994917).length < 2 ^ (prefixWord ++ tailWord_3994917).sum := by decide
  have hdescent : baseEnd_3994917 < baseStart_3994917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994931 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 3, 2, 2]
def baseStart_3994931 : Nat := 118140960795 + 3994931 * 2 ^ 59
def prefixEnd_3994931 : Nat := 4983230072969 + 3 ^ 40 * 3994931 * 2
def baseEnd_3994931 : Nat := 2051319784546814547790153

theorem tailTrace_3994931 : CollatzResearch.WordTrace tailWord_3994931 prefixEnd_3994931 2051319784546814547790153 := by
  unfold tailWord_3994931
  simp only [CollatzResearch.WordTrace]
  refine ⟨145707103890054741740832647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97138069260036494493888431 145707103890054741740832647)
  ·
    refine ⟨218560655835082112611248971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145707103890054741740832647 218560655835082112611248971)
    ·
      refine ⟨327840983752623168916873457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218560655835082112611248971 327840983752623168916873457)
      ·
        refine ⟨245880737814467376687655093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327840983752623168916873457 245880737814467376687655093)
        ·
          refine ⟨23051319170106316564467665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 245880737814467376687655093 23051319170106316564467665)
          ·
            refine ⟨17288489377579737423350749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23051319170106316564467665 17288489377579737423350749)
            ·
              refine ⟨6483183516592401533756531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17288489377579737423350749 6483183516592401533756531)
              ·
                refine ⟨9724775274888602300634797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483183516592401533756531 9724775274888602300634797)
                ·
                  refine ⟨3646790728083225862738049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9724775274888602300634797 3646790728083225862738049)
                  ·
                    refine ⟨2735093046062419397053537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3646790728083225862738049 2735093046062419397053537)
                    ·
                      refine ⟨2051319784546814547790153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735093046062419397053537 2051319784546814547790153)
                      ·
                        rfl

theorem cell23_3994931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 2, 2].length) (baseStart_3994931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994931 prefixEnd_3994931 := by exact prefixLift 3994931
  have htrace : WordTrace (prefixWord ++ tailWord_3994931) baseStart_3994931 baseEnd_3994931 := by
    simpa [prefixWord, tailWord_3994931, baseEnd_3994931] using wordTrace_append hprefix tailTrace_3994931
  have hstable : (prefixWord ++ tailWord_3994931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994931).length < 2 ^ (prefixWord ++ tailWord_3994931).sum := by decide
  have hdescent : baseEnd_3994931 < baseStart_3994931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994947 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3]
def baseStart_3994947 : Nat := 118140960795 + 3994947 * 2 ^ 59
def prefixEnd_3994947 : Nat := 4983230072969 + 3 ^ 40 * 3994947 * 2
def baseEnd_3994947 : Nat := 2051328000237286485190079

theorem tailTrace_3994947 : CollatzResearch.WordTrace tailWord_3994947 prefixEnd_3994947 2051328000237286485190079 := by
  unfold tailWord_3994947
  simp only [CollatzResearch.WordTrace]
  refine ⟨145707687457996776473415095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97138458305331184315610063 145707687457996776473415095)
  ·
    refine ⟨218561531186995164710122643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145707687457996776473415095 218561531186995164710122643)
    ·
      refine ⟨327842296780492747065183965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218561531186995164710122643 327842296780492747065183965)
      ·
        refine ⟨122940861292684780149443987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327842296780492747065183965 122940861292684780149443987)
        ·
          refine ⟨184411291939027170224165981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122940861292684780149443987 184411291939027170224165981)
          ·
            refine ⟨69154234477135188834062243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184411291939027170224165981 69154234477135188834062243)
            ·
              refine ⟨103731351715702783251093365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69154234477135188834062243 103731351715702783251093365)
              ·
                refine ⟨9724814223347135929790003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103731351715702783251093365 9724814223347135929790003)
                ·
                  refine ⟨14587221335020703894685005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724814223347135929790003 14587221335020703894685005)
                  ·
                    refine ⟨5470208000632763960506877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14587221335020703894685005 5470208000632763960506877)
                    ·
                      refine ⟨2051328000237286485190079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470208000632763960506877 2051328000237286485190079)
                      ·
                        rfl

theorem cell23_3994947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_3994947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994947 prefixEnd_3994947 := by exact prefixLift 3994947
  have htrace : WordTrace (prefixWord ++ tailWord_3994947) baseStart_3994947 baseEnd_3994947 := by
    simpa [prefixWord, tailWord_3994947, baseEnd_3994947] using wordTrace_append hprefix tailTrace_3994947
  have hstable : (prefixWord ++ tailWord_3994947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994947).length < 2 ^ (prefixWord ++ tailWord_3994947).sum := by decide
  have hdescent : baseEnd_3994947 < baseStart_3994947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994948 : List Nat := [2, 3, 4, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3994948 : Nat := 118140960795 + 3994948 * 2 ^ 59
def prefixEnd_3994948 : Nat := 4983230072969 + 3 ^ 40 * 3994948 * 2
def baseEnd_3994948 : Nat := 2051328513717940981277575

theorem tailTrace_3994948 : CollatzResearch.WordTrace tailWord_3994948 prefixEnd_3994948 2051328513717940981277575 := by
  unfold tailWord_3994948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72853861965496576822100749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97138482620662102429467665 72853861965496576822100749)
  ·
    refine ⟨27320198237061216308287781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72853861965496576822100749 27320198237061216308287781)
    ·
      refine ⟨5122537169448978057803959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27320198237061216308287781 5122537169448978057803959)
      ·
        refine ⟨7683805754173467086705939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5122537169448978057803959 7683805754173467086705939)
        ·
          refine ⟨11525708631260200630058909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683805754173467086705939 11525708631260200630058909)
          ·
            refine ⟨4322140736722575236272091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11525708631260200630058909 4322140736722575236272091)
            ·
              refine ⟨6483211105083862854408137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322140736722575236272091 6483211105083862854408137)
              ·
                refine ⟨4862408328812897140806103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483211105083862854408137 4862408328812897140806103)
                ·
                  refine ⟨7293612493219345711209155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862408328812897140806103 7293612493219345711209155)
                  ·
                    refine ⟨10940418739829018566813733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7293612493219345711209155 10940418739829018566813733)
                    ·
                      refine ⟨2051328513717940981277575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10940418739829018566813733 2051328513717940981277575)
                      ·
                        rfl

theorem cell23_3994948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3994948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994948 prefixEnd_3994948 := by exact prefixLift 3994948
  have htrace : WordTrace (prefixWord ++ tailWord_3994948) baseStart_3994948 baseEnd_3994948 := by
    simpa [prefixWord, tailWord_3994948, baseEnd_3994948] using wordTrace_append hprefix tailTrace_3994948
  have hstable : (prefixWord ++ tailWord_3994948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994948).length < 2 ^ (prefixWord ++ tailWord_3994948).sum := by decide
  have hdescent : baseEnd_3994948 < baseStart_3994948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994951 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_3994951 : Nat := 118140960795 + 3994951 * 2 ^ 59
def prefixEnd_3994951 : Nat := 4983230072969 + 3 ^ 40 * 3994951 * 2
def baseEnd_3994951 : Nat := 2051330054159904469540061

theorem tailTrace_3994951 : CollatzResearch.WordTrace tailWord_3994951 prefixEnd_3994951 2051330054159904469540061 := by
  unfold tailWord_3994951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145707833349982285156560707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97138555566654856771040471 145707833349982285156560707)
  ·
    refine ⟨218561750024973427734841061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145707833349982285156560707 218561750024973427734841061)
    ·
      refine ⟨40980328129682517700282699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 218561750024973427734841061 40980328129682517700282699)
      ·
        refine ⟨61470492194523776550424049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40980328129682517700282699 61470492194523776550424049)
        ·
          refine ⟨46102869145892832412818037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61470492194523776550424049 46102869145892832412818037)
          ·
            refine ⟨4322143982427453038701691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46102869145892832412818037 4322143982427453038701691)
            ·
              refine ⟨6483215973641179558052537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322143982427453038701691 6483215973641179558052537)
              ·
                refine ⟨4862411980230884668539403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483215973641179558052537 4862411980230884668539403)
                ·
                  refine ⟨7293617970346327002809105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4862411980230884668539403 7293617970346327002809105)
                  ·
                    refine ⟨5470213477759745252106829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7293617970346327002809105 5470213477759745252106829)
                    ·
                      refine ⟨2051330054159904469540061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470213477759745252106829 2051330054159904469540061)
                      ·
                        rfl

theorem cell23_3994951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_3994951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994951 prefixEnd_3994951 := by exact prefixLift 3994951
  have htrace : WordTrace (prefixWord ++ tailWord_3994951) baseStart_3994951 baseEnd_3994951 := by
    simpa [prefixWord, tailWord_3994951, baseEnd_3994951] using wordTrace_append hprefix tailTrace_3994951
  have hstable : (prefixWord ++ tailWord_3994951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994951).length < 2 ^ (prefixWord ++ tailWord_3994951).sum := by decide
  have hdescent : baseEnd_3994951 < baseStart_3994951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994964 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3994964 : Nat := 118140960795 + 3994964 * 2 ^ 59
def prefixEnd_3994964 : Nat := 4983230072969 + 3 ^ 40 * 3994964 * 2
def baseEnd_3994964 : Nat := 2051336729408412918677501

theorem tailTrace_3994964 : CollatzResearch.WordTrace tailWord_3994964 prefixEnd_3994964 2051336729408412918677501 := by
  unfold tailWord_3994964
  simp only [CollatzResearch.WordTrace]
  refine ⟨72854153749467594188391973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97138871665956792251189297 72854153749467594188391973)
  ·
    refine ⟨13660153828025173910323495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72854153749467594188391973 13660153828025173910323495)
    ·
      refine ⟨20490230742037760865485243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13660153828025173910323495 20490230742037760865485243)
      ·
        refine ⟨30735346113056641298227865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20490230742037760865485243 30735346113056641298227865)
        ·
          refine ⟨23051509584792480973670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30735346113056641298227865 23051509584792480973670899)
          ·
            refine ⟨34577264377188721460506349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23051509584792480973670899 34577264377188721460506349)
            ·
              refine ⟨12966474141445770547689881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34577264377188721460506349 12966474141445770547689881)
              ·
                refine ⟨9724855606084327910767411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12966474141445770547689881 9724855606084327910767411)
                ·
                  refine ⟨14587283409126491866151117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9724855606084327910767411 14587283409126491866151117)
                  ·
                    refine ⟨5470231278422434449806669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14587283409126491866151117 5470231278422434449806669)
                    ·
                      refine ⟨2051336729408412918677501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470231278422434449806669 2051336729408412918677501)
                      ·
                        rfl

theorem cell23_3994964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3994964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994964 prefixEnd_3994964 := by exact prefixLift 3994964
  have htrace : WordTrace (prefixWord ++ tailWord_3994964) baseStart_3994964 baseEnd_3994964 := by
    simpa [prefixWord, tailWord_3994964, baseEnd_3994964] using wordTrace_append hprefix tailTrace_3994964
  have hstable : (prefixWord ++ tailWord_3994964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994964).length < 2 ^ (prefixWord ++ tailWord_3994964).sum := by decide
  have hdescent : baseEnd_3994964 < baseStart_3994964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3994981 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3994981 : Nat := 118140960795 + 3994981 * 2 ^ 59
def prefixEnd_3994981 : Nat := 4983230072969 + 3 ^ 40 * 3994981 * 2
def baseEnd_3994981 : Nat := 2051345458579539352164923

theorem tailTrace_3994981 : CollatzResearch.WordTrace tailWord_3994981 prefixEnd_3994981 2051345458579539352164923 := by
  unfold tailWord_3994981
  simp only [CollatzResearch.WordTrace]
  refine ⟨145708927539873600280152797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97139285026582400186768531 145708927539873600280152797)
  ·
    refine ⟨54640847827452600105057299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145708927539873600280152797 54640847827452600105057299)
    ·
      refine ⟨81961271741178900157585949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54640847827452600105057299 81961271741178900157585949)
      ·
        refine ⟨30735476902942087559094731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81961271741178900157585949 30735476902942087559094731)
        ·
          refine ⟨46103215354413131338642097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30735476902942087559094731 46103215354413131338642097)
          ·
            refine ⟨34577411515809848503981573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46103215354413131338642097 34577411515809848503981573)
            ·
              refine ⟨6483264659214346594496545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34577411515809848503981573 6483264659214346594496545)
              ·
                refine ⟨4862448494410759945872409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6483264659214346594496545 4862448494410759945872409)
                ·
                  refine ⟨3646836370808069959404307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4862448494410759945872409 3646836370808069959404307)
                  ·
                    refine ⟨5470254556212104939106461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3646836370808069959404307 5470254556212104939106461)
                    ·
                      refine ⟨2051345458579539352164923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470254556212104939106461 2051345458579539352164923)
                      ·
                        rfl

theorem cell23_3994981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3994981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3994981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3994981 prefixEnd_3994981 := by exact prefixLift 3994981
  have htrace : WordTrace (prefixWord ++ tailWord_3994981) baseStart_3994981 baseEnd_3994981 := by
    simpa [prefixWord, tailWord_3994981, baseEnd_3994981] using wordTrace_append hprefix tailTrace_3994981
  have hstable : (prefixWord ++ tailWord_3994981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3994981).length < 2 ^ (prefixWord ++ tailWord_3994981).sum := by decide
  have hdescent : baseEnd_3994981 < baseStart_3994981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3994981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995057 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_3995057 : Nat := 118140960795 + 3995057 * 2 ^ 59
def prefixEnd_3995057 : Nat := 4983230072969 + 3 ^ 40 * 3995057 * 2
def baseEnd_3995057 : Nat := 683794827703093684938191

theorem tailTrace_3995057 : CollatzResearch.WordTrace tailWord_3995057 prefixEnd_3995057 683794827703093684938191 := by
  unfold tailWord_3995057
  simp only [CollatzResearch.WordTrace]
  refine ⟨145711699487598265259919425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97141132991732176839946283 145711699487598265259919425)
  ·
    refine ⟨109283774615698698944939569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145711699487598265259919425 109283774615698698944939569)
    ·
      refine ⟨81962830961774024208704677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109283774615698698944939569 81962830961774024208704677)
      ·
        refine ⟨15368030805332629539132127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81962830961774024208704677 15368030805332629539132127)
        ·
          refine ⟨23052046207998944308698191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368030805332629539132127 23052046207998944308698191)
          ·
            refine ⟨34578069311998416463047287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052046207998944308698191 34578069311998416463047287)
            ·
              refine ⟨51867103967997624694570931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34578069311998416463047287 51867103967997624694570931)
              ·
                refine ⟨77800655951996437041856397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51867103967997624694570931 77800655951996437041856397)
                ·
                  refine ⟨29175245981998663890696149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77800655951996437041856397 29175245981998663890696149)
                  ·
                    refine ⟨683794827703093684938191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29175245981998663890696149 683794827703093684938191)
                    ·
                      rfl

theorem cell23_3995057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_3995057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995057 prefixEnd_3995057 := by exact prefixLift 3995057
  have htrace : WordTrace (prefixWord ++ tailWord_3995057) baseStart_3995057 baseEnd_3995057 := by
    simpa [prefixWord, tailWord_3995057, baseEnd_3995057] using wordTrace_append hprefix tailTrace_3995057
  have hstable : (prefixWord ++ tailWord_3995057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995057).length < 2 ^ (prefixWord ++ tailWord_3995057).sum := by decide
  have hdescent : baseEnd_3995057 < baseStart_3995057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995064 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_3995064 : Nat := 118140960795 + 3995064 * 2 ^ 59
def prefixEnd_3995064 : Nat := 4983230072969 + 3 ^ 40 * 3995064 * 2
def baseEnd_3995064 : Nat := 2051388077473862527427041

theorem tailTrace_3995064 : CollatzResearch.WordTrace tailWord_3995064 prefixEnd_3995064 2051388077473862527427041 := by
  unfold tailWord_3995064
  simp only [CollatzResearch.WordTrace]
  refine ⟨72855977399286452727712123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97141303199048603636949497 72855977399286452727712123)
  ·
    refine ⟨109283966098929679091568185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72855977399286452727712123 109283966098929679091568185)
    ·
      refine ⟨81962974574197259318676139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109283966098929679091568185 81962974574197259318676139)
      ·
        refine ⟨122944461861295888978014209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81962974574197259318676139 122944461861295888978014209)
        ·
          refine ⟨92208346395971916733510657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122944461861295888978014209 92208346395971916733510657)
          ·
            refine ⟨69156259796978937550132993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92208346395971916733510657 69156259796978937550132993)
            ·
              refine ⟨51867194847734203162599745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69156259796978937550132993 51867194847734203162599745)
              ·
                refine ⟨38900396135800652371949809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51867194847734203162599745 38900396135800652371949809)
                ·
                  refine ⟨29175297101850489278962357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38900396135800652371949809 29175297101850489278962357)
                  ·
                    refine ⟨2735184103298483369902721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29175297101850489278962357 2735184103298483369902721)
                    ·
                      refine ⟨2051388077473862527427041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735184103298483369902721 2051388077473862527427041)
                      ·
                        rfl

theorem cell23_3995064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_3995064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995064 prefixEnd_3995064 := by exact prefixLift 3995064
  have htrace : WordTrace (prefixWord ++ tailWord_3995064) baseStart_3995064 baseEnd_3995064 := by
    simpa [prefixWord, tailWord_3995064, baseEnd_3995064] using wordTrace_append hprefix tailTrace_3995064
  have hstable : (prefixWord ++ tailWord_3995064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995064).length < 2 ^ (prefixWord ++ tailWord_3995064).sum := by decide
  have hdescent : baseEnd_3995064 < baseStart_3995064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995104 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_3995104 : Nat := 118140960795 + 3995104 * 2 ^ 59
def prefixEnd_3995104 : Nat := 4983230072969 + 3 ^ 40 * 3995104 * 2
def baseEnd_3995104 : Nat := 683802872233347456975619

theorem tailTrace_3995104 : CollatzResearch.WordTrace tailWord_3995104 prefixEnd_3995104 683802872233347456975619 := by
  unfold tailWord_3995104
  simp only [CollatzResearch.WordTrace]
  refine ⟨72856706859213996143440183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97142275812285328191253577 72856706859213996143440183)
  ·
    refine ⟨109285060288820994215160275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72856706859213996143440183 109285060288820994215160275)
    ·
      refine ⟨163927590433231491322740413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109285060288820994215160275 163927590433231491322740413)
      ·
        refine ⟨61472846412461809246027655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163927590433231491322740413 61472846412461809246027655)
        ·
          refine ⟨92209269618692713869041483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61472846412461809246027655 92209269618692713869041483)
          ·
            refine ⟨138313904428039070803562225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92209269618692713869041483 138313904428039070803562225)
            ·
              refine ⟨103735428321029303102671669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138313904428039070803562225 103735428321029303102671669)
              ·
                refine ⟨9725196405096497165875469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103735428321029303102671669 9725196405096497165875469)
                ·
                  refine ⟨3646948651911186437203301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9725196405096497165875469 3646948651911186437203301)
                  ·
                    refine ⟨683802872233347456975619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646948651911186437203301 683802872233347456975619)
                    ·
                      rfl

theorem cell23_3995104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_3995104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995104 prefixEnd_3995104 := by exact prefixLift 3995104
  have htrace : WordTrace (prefixWord ++ tailWord_3995104) baseStart_3995104 baseEnd_3995104 := by
    simpa [prefixWord, tailWord_3995104, baseEnd_3995104] using wordTrace_append hprefix tailTrace_3995104
  have hstable : (prefixWord ++ tailWord_3995104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995104).length < 2 ^ (prefixWord ++ tailWord_3995104).sum := by decide
  have hdescent : baseEnd_3995104 < baseStart_3995104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995155 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 1, 4]
def baseStart_3995155 : Nat := 118140960795 + 3995155 * 2 ^ 59
def prefixEnd_3995155 : Nat := 4983230072969 + 3 ^ 40 * 3995155 * 2
def baseEnd_3995155 : Nat := 683811601404473890463041

theorem tailTrace_3995155 : CollatzResearch.WordTrace tailWord_3995155 prefixEnd_3995155 683811601404473890463041 := by
  unfold tailWord_3995155
  simp only [CollatzResearch.WordTrace]
  refine ⟨145715273841243227996986919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97143515894162151997991279 145715273841243227996986919)
  ·
    refine ⟨218572910761864841995480379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145715273841243227996986919 218572910761864841995480379)
    ·
      refine ⟨327859366142797262993220569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218572910761864841995480379 327859366142797262993220569)
      ·
        refine ⟨245894524607097947244915427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327859366142797262993220569 245894524607097947244915427)
        ·
          refine ⟨368841786910646920867373141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245894524607097947244915427 368841786910646920867373141)
          ·
            refine ⟨4322364690359143603914529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 368841786910646920867373141 4322364690359143603914529)
            ·
              refine ⟨3241773517769357702935897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322364690359143603914529 3241773517769357702935897)
              ·
                refine ⟨2431330138327018277201923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3241773517769357702935897 2431330138327018277201923)
                ·
                  refine ⟨3646995207490527415802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431330138327018277201923 3646995207490527415802885)
                  ·
                    refine ⟨683811601404473890463041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3646995207490527415802885 683811601404473890463041)
                    ·
                      rfl

theorem cell23_3995155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 4].length) (baseStart_3995155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995155 prefixEnd_3995155 := by exact prefixLift 3995155
  have htrace : WordTrace (prefixWord ++ tailWord_3995155) baseStart_3995155 baseEnd_3995155 := by
    simpa [prefixWord, tailWord_3995155, baseEnd_3995155] using wordTrace_append hprefix tailTrace_3995155
  have hstable : (prefixWord ++ tailWord_3995155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995155).length < 2 ^ (prefixWord ++ tailWord_3995155).sum := by decide
  have hdescent : baseEnd_3995155 < baseStart_3995155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995164 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3995164 : Nat := 118140960795 + 3995164 * 2 ^ 59
def prefixEnd_3995164 : Nat := 4983230072969 + 3 ^ 40 * 3995164 * 2
def baseEnd_3995164 : Nat := 683813141846437378725527

theorem tailTrace_3995164 : CollatzResearch.WordTrace tailWord_3995164 prefixEnd_3995164 683813141846437378725527 := by
  unfold tailWord_3995164
  simp only [CollatzResearch.WordTrace]
  refine ⟨72857801049105311267032273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97143734732140415022709697 72857801049105311267032273)
  ·
    refine ⟨54643350786828983450274205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72857801049105311267032273 54643350786828983450274205)
    ·
      refine ⟨20491256545060868793852827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54643350786828983450274205 20491256545060868793852827)
      ·
        refine ⟨30736884817591303190779241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20491256545060868793852827 30736884817591303190779241)
        ·
          refine ⟨23052663613193477393084431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30736884817591303190779241 23052663613193477393084431)
          ·
            refine ⟨34578995419790216089626647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052663613193477393084431 34578995419790216089626647)
            ·
              refine ⟨51868493129685324134439971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34578995419790216089626647 51868493129685324134439971)
              ·
                refine ⟨77802739694527986201659957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51868493129685324134439971 77802739694527986201659957)
                ·
                  refine ⟨7294006846361998706405621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77802739694527986201659957 7294006846361998706405621)
                  ·
                    refine ⟨683813141846437378725527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7294006846361998706405621 683813141846437378725527)
                    ·
                      rfl

theorem cell23_3995164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3995164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995164 prefixEnd_3995164 := by exact prefixLift 3995164
  have htrace : WordTrace (prefixWord ++ tailWord_3995164) baseStart_3995164 baseEnd_3995164 := by
    simpa [prefixWord, tailWord_3995164, baseEnd_3995164] using wordTrace_append hprefix tailTrace_3995164
  have hstable : (prefixWord ++ tailWord_3995164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995164).length < 2 ^ (prefixWord ++ tailWord_3995164).sum := by decide
  have hdescent : baseEnd_3995164 < baseStart_3995164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995178 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3995178 : Nat := 118140960795 + 3995178 * 2 ^ 59
def prefixEnd_3995178 : Nat := 4983230072969 + 3 ^ 40 * 3995178 * 2
def baseEnd_3995178 : Nat := 2051446614268475081401517

theorem tailTrace_3995178 : CollatzResearch.WordTrace tailWord_3995178 prefixEnd_3995178 2051446614268475081401517 := by
  unfold tailWord_3995178
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429028180039975731268547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97144075146773268616716125 36429028180039975731268547)
  ·
    refine ⟨54643542270059963596902821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36429028180039975731268547 54643542270059963596902821)
    ·
      refine ⟨10245664175636243174419279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54643542270059963596902821 10245664175636243174419279)
      ·
        refine ⟨15368496263454364761628919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245664175636243174419279 15368496263454364761628919)
        ·
          refine ⟨23052744395181547142443379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15368496263454364761628919 23052744395181547142443379)
          ·
            refine ⟨34579116592772320713665069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23052744395181547142443379 34579116592772320713665069)
            ·
              refine ⟨12967168722289620267624401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34579116592772320713665069 12967168722289620267624401)
              ·
                refine ⟨9725376541717215200718301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12967168722289620267624401 9725376541717215200718301)
                ·
                  refine ⟨3647016203143955700269363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9725376541717215200718301 3647016203143955700269363)
                  ·
                    refine ⟨5470524304715933550404045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3647016203143955700269363 5470524304715933550404045)
                    ·
                      refine ⟨2051446614268475081401517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470524304715933550404045 2051446614268475081401517)
                      ·
                        rfl

theorem cell23_3995178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3995178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995178 prefixEnd_3995178 := by exact prefixLift 3995178
  have htrace : WordTrace (prefixWord ++ tailWord_3995178) baseStart_3995178 baseEnd_3995178 := by
    simpa [prefixWord, tailWord_3995178, baseEnd_3995178] using wordTrace_append hprefix tailTrace_3995178
  have hstable : (prefixWord ++ tailWord_3995178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995178).length < 2 ^ (prefixWord ++ tailWord_3995178).sum := by decide
  have hdescent : baseEnd_3995178 < baseStart_3995178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995194 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_3995194 : Nat := 118140960795 + 3995194 * 2 ^ 59
def prefixEnd_3995194 : Nat := 4983230072969 + 3 ^ 40 * 3995194 * 2
def baseEnd_3995194 : Nat := 683818276652982339600481

theorem tailTrace_3995194 : CollatzResearch.WordTrace tailWord_3995194 prefixEnd_3995194 683818276652982339600481 := by
  unfold tailWord_3995194
  simp only [CollatzResearch.WordTrace]
  refine ⟨36429174072025484414414159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97144464192067958438437757 36429174072025484414414159)
  ·
    refine ⟨54643761108038226621621239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36429174072025484414414159 54643761108038226621621239)
    ·
      refine ⟨81965641662057339932431859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54643761108038226621621239 81965641662057339932431859)
      ·
        refine ⟨122948462493086009898647789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81965641662057339932431859 122948462493086009898647789)
        ·
          refine ⟨46105673434907253711992921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122948462493086009898647789 46105673434907253711992921)
          ·
            refine ⟨34579255076180440283994691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46105673434907253711992921 34579255076180440283994691)
            ·
              refine ⟨51868882614270660425992037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34579255076180440283994691 51868882614270660425992037)
              ·
                refine ⟨9725415490175748829873507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51868882614270660425992037 9725415490175748829873507)
                ·
                  refine ⟨14588123235263623244810261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9725415490175748829873507 14588123235263623244810261)
                  ·
                    refine ⟨683818276652982339600481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14588123235263623244810261 683818276652982339600481)
                    ·
                      rfl

theorem cell23_3995194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_3995194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995194 prefixEnd_3995194 := by exact prefixLift 3995194
  have htrace : WordTrace (prefixWord ++ tailWord_3995194) baseStart_3995194 baseEnd_3995194 := by
    simpa [prefixWord, tailWord_3995194, baseEnd_3995194] using wordTrace_append hprefix tailTrace_3995194
  have hstable : (prefixWord ++ tailWord_3995194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995194).length < 2 ^ (prefixWord ++ tailWord_3995194).sum := by decide
  have hdescent : baseEnd_3995194 < baseStart_3995194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995214 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3995214 : Nat := 118140960795 + 3995214 * 2 ^ 59
def prefixEnd_3995214 : Nat := 4983230072969 + 3 ^ 40 * 3995214 * 2
def baseEnd_3995214 : Nat := 2051465099572036940551351

theorem tailTrace_3995214 : CollatzResearch.WordTrace tailWord_3995214 prefixEnd_3995214 2051465099572036940551351 := by
  unfold tailWord_3995214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18214678218503685134173087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97144950498686320715589797 18214678218503685134173087)
  ·
    refine ⟨27322017327755527701259631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18214678218503685134173087 27322017327755527701259631)
    ·
      refine ⟨40983025991633291551889447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27322017327755527701259631 40983025991633291551889447)
      ·
        refine ⟨61474538987449937327834171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40983025991633291551889447 61474538987449937327834171)
        ·
          refine ⟨92211808481174905991751257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61474538987449937327834171 92211808481174905991751257)
          ·
            refine ⟨69158856360881179493813443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92211808481174905991751257 69158856360881179493813443)
            ·
              refine ⟨103738284541321769240720165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69158856360881179493813443 103738284541321769240720165)
              ·
                refine ⟨19450928351497831732635031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103738284541321769240720165 19450928351497831732635031)
                ·
                  refine ⟨29176392527246747598952547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19450928351497831732635031 29176392527246747598952547)
                  ·
                    refine ⟨43764588790870121398428821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29176392527246747598952547 43764588790870121398428821)
                    ·
                      refine ⟨2051465099572036940551351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43764588790870121398428821 2051465099572036940551351)
                      ·
                        rfl

theorem cell23_3995214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3995214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995214 prefixEnd_3995214 := by exact prefixLift 3995214
  have htrace : WordTrace (prefixWord ++ tailWord_3995214) baseStart_3995214 baseEnd_3995214 := by
    simpa [prefixWord, tailWord_3995214, baseEnd_3995214] using wordTrace_append hprefix tailTrace_3995214
  have hstable : (prefixWord ++ tailWord_3995214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995214).length < 2 ^ (prefixWord ++ tailWord_3995214).sum := by decide
  have hdescent : baseEnd_3995214 < baseStart_3995214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995228 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3995228 : Nat := 118140960795 + 3995228 * 2 ^ 59
def prefixEnd_3995228 : Nat := 4983230072969 + 3 ^ 40 * 3995228 * 2
def baseEnd_3995228 : Nat := 683824096100399961925429

theorem tailTrace_3995228 : CollatzResearch.WordTrace tailWord_3995228 prefixEnd_3995228 683824096100399961925429 := by
  unfold tailWord_3995228
  simp only [CollatzResearch.WordTrace]
  refine ⟨72858968184989380732197169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97145290913319174309596225 72858968184989380732197169)
  ·
    refine ⟨54644226138742035549147877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72858968184989380732197169 54644226138742035549147877)
    ·
      refine ⟨10245792401014131665465227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54644226138742035549147877 10245792401014131665465227)
      ·
        refine ⟨15368688601521197498197841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10245792401014131665465227 15368688601521197498197841)
        ·
          refine ⟨11526516451140898123648381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15368688601521197498197841 11526516451140898123648381)
          ·
            refine ⟨4322443669177836796368143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11526516451140898123648381 4322443669177836796368143)
            ·
              refine ⟨6483665503766755194552215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322443669177836796368143 6483665503766755194552215)
              ·
                refine ⟨9725498255650132791828323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6483665503766755194552215 9725498255650132791828323)
                ·
                  refine ⟨14588247383475199187742485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9725498255650132791828323 14588247383475199187742485)
                  ·
                    refine ⟨683824096100399961925429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14588247383475199187742485 683824096100399961925429)
                    ·
                      rfl

theorem cell23_3995228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3995228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995228 prefixEnd_3995228 := by exact prefixLift 3995228
  have htrace : WordTrace (prefixWord ++ tailWord_3995228) baseStart_3995228 baseEnd_3995228 := by
    simpa [prefixWord, tailWord_3995228, baseEnd_3995228] using wordTrace_append hprefix tailTrace_3995228
  have hstable : (prefixWord ++ tailWord_3995228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995228).length < 2 ^ (prefixWord ++ tailWord_3995228).sum := by decide
  have hdescent : baseEnd_3995228 < baseStart_3995228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995264 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3995264 : Nat := 118140960795 + 3995264 * 2 ^ 59
def prefixEnd_3995264 : Nat := 4983230072969 + 3 ^ 40 * 3995264 * 2
def baseEnd_3995264 : Nat := 2051490773604761744926121

theorem tailTrace_3995264 : CollatzResearch.WordTrace tailWord_3995264 prefixEnd_3995264 2051490773604761744926121 := by
  unfold tailWord_3995264
  simp only [CollatzResearch.WordTrace]
  refine ⟨72859624698924169806352423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97146166265232226408469897 72859624698924169806352423)
  ·
    refine ⟨109289437048386254709528635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72859624698924169806352423 109289437048386254709528635)
    ·
      refine ⟨163934155572579382064292953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109289437048386254709528635 163934155572579382064292953)
      ·
        refine ⟨122950616679434536548219715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163934155572579382064292953 122950616679434536548219715)
        ·
          refine ⟨184425925019151804822329573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122950616679434536548219715 184425925019151804822329573)
          ·
            refine ⟨34579860941090963404186795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184425925019151804822329573 34579860941090963404186795)
            ·
              refine ⟨51869791411636445106280193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34579860941090963404186795 51869791411636445106280193)
              ·
                refine ⟨38902343558727333829710145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51869791411636445106280193 38902343558727333829710145)
                ·
                  refine ⟨29176757669045500372282609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38902343558727333829710145 29176757669045500372282609)
                  ·
                    refine ⟨21882568251784125279211957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29176757669045500372282609 21882568251784125279211957)
                    ·
                      refine ⟨2051490773604761744926121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21882568251784125279211957 2051490773604761744926121)
                      ·
                        rfl

theorem cell23_3995264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3995264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995264 prefixEnd_3995264 := by exact prefixLift 3995264
  have htrace : WordTrace (prefixWord ++ tailWord_3995264) baseStart_3995264 baseEnd_3995264 := by
    simpa [prefixWord, tailWord_3995264, baseEnd_3995264] using wordTrace_append hprefix tailTrace_3995264
  have hstable : (prefixWord ++ tailWord_3995264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995264).length < 2 ^ (prefixWord ++ tailWord_3995264).sum := by decide
  have hdescent : baseEnd_3995264 < baseStart_3995264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995338 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_3995338 : Nat := 118140960795 + 3995338 * 2 ^ 59
def prefixEnd_3995338 : Nat := 4983230072969 + 3 ^ 40 * 3995338 * 2
def baseEnd_3995338 : Nat := 2051528771173194455400781

theorem tailTrace_3995338 : CollatzResearch.WordTrace tailWord_3995338 prefixEnd_3995338 2051528771173194455400781 := by
  unfold tailWord_3995338
  simp only [CollatzResearch.WordTrace]
  refine ⟨36430487099895062562724667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97147965599720166833932445 36430487099895062562724667)
  ·
    refine ⟨54645730649842593844087001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36430487099895062562724667 54645730649842593844087001)
    ·
      refine ⟨40984297987381945383065251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54645730649842593844087001 40984297987381945383065251)
      ·
        refine ⟨61476446981072918074597877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40984297987381945383065251 61476446981072918074597877)
        ·
          refine ⟨5763416904475586069493551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61476446981072918074597877 5763416904475586069493551)
          ·
            refine ⟨8645125356713379104240327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5763416904475586069493551 8645125356713379104240327)
            ·
              refine ⟨12967688035070068656360491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645125356713379104240327 12967688035070068656360491)
              ·
                refine ⟨19451532052605102984540737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12967688035070068656360491 19451532052605102984540737)
                ·
                  refine ⟨14588649039453827238405553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19451532052605102984540737 14588649039453827238405553)
                  ·
                    refine ⟨10941486779590370428804165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14588649039453827238405553 10941486779590370428804165)
                    ·
                      refine ⟨2051528771173194455400781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10941486779590370428804165 2051528771173194455400781)
                      ·
                        rfl

theorem cell23_3995338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_3995338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995338 prefixEnd_3995338 := by exact prefixLift 3995338
  have htrace : WordTrace (prefixWord ++ tailWord_3995338) baseStart_3995338 baseEnd_3995338 := by
    simpa [prefixWord, tailWord_3995338, baseEnd_3995338] using wordTrace_append hprefix tailTrace_3995338
  have hstable : (prefixWord ++ tailWord_3995338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995338).length < 2 ^ (prefixWord ++ tailWord_3995338).sum := by decide
  have hdescent : baseEnd_3995338 < baseStart_3995338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995348 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 7]
def baseStart_3995348 : Nat := 118140960795 + 3995348 * 2 ^ 59
def prefixEnd_3995348 : Nat := 4983230072969 + 3 ^ 40 * 3995348 * 2
def baseEnd_3995348 : Nat := 227948211775526601808415

theorem tailTrace_3995348 : CollatzResearch.WordTrace tailWord_3995348 prefixEnd_3995348 227948211775526601808415 := by
  unfold tailWord_3995348
  simp only [CollatzResearch.WordTrace]
  refine ⟨72861156564772010979381349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97148208753029347972508465 72861156564772010979381349)
  ·
    refine ⟨13661466855894752058634003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72861156564772010979381349 13661466855894752058634003)
    ·
      refine ⟨20492200283842128087951005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13661466855894752058634003 20492200283842128087951005)
      ·
        refine ⟨7684575106440798032981627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20492200283842128087951005 7684575106440798032981627)
        ·
          refine ⟨11526862659661197049472441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7684575106440798032981627 11526862659661197049472441)
          ·
            refine ⟨8645146994745897787104331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11526862659661197049472441 8645146994745897787104331)
            ·
              refine ⟨12967720492118846680656497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8645146994745897787104331 12967720492118846680656497)
              ·
                refine ⟨9725790369089135010492373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12967720492118846680656497 9725790369089135010492373)
                ·
                  refine ⟨227948211775526601808415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9725790369089135010492373 227948211775526601808415)
                  ·
                    rfl

theorem cell23_3995348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_3995348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995348 prefixEnd_3995348 := by exact prefixLift 3995348
  have htrace : WordTrace (prefixWord ++ tailWord_3995348) baseStart_3995348 baseEnd_3995348 := by
    simpa [prefixWord, tailWord_3995348, baseEnd_3995348] using wordTrace_append hprefix tailTrace_3995348
  have hstable : (prefixWord ++ tailWord_3995348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995348).length < 2 ^ (prefixWord ++ tailWord_3995348).sum := by decide
  have hdescent : baseEnd_3995348 < baseStart_3995348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995418 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_3995418 : Nat := 118140960795 + 3995418 * 2 ^ 59
def prefixEnd_3995418 : Nat := 4983230072969 + 3 ^ 40 * 3995418 * 2
def baseEnd_3995418 : Nat := 2051569849625554142400413

theorem tailTrace_3995418 : CollatzResearch.WordTrace tailWord_3995418 prefixEnd_3995418 2051569849625554142400413 := by
  unfold tailWord_3995418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36431216559822605978452727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97149910826193615942540605 36431216559822605978452727)
  ·
    refine ⟨54646824839733908967679091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36431216559822605978452727 54646824839733908967679091)
    ·
      refine ⟨81970237259600863451518637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54646824839733908967679091 81970237259600863451518637)
      ·
        refine ⟨30738838972350323794319489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81970237259600863451518637 30738838972350323794319489)
        ·
          refine ⟨23054129229262742845739617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30738838972350323794319489 23054129229262742845739617)
          ·
            refine ⟨17290596921947057134304713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23054129229262742845739617 17290596921947057134304713)
            ·
              refine ⟨12967947691460292850728535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17290596921947057134304713 12967947691460292850728535)
              ·
                refine ⟨19451921537190439276092803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12967947691460292850728535 19451921537190439276092803)
                ·
                  refine ⟨29177882305785658914139205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19451921537190439276092803 29177882305785658914139205)
                  ·
                    refine ⟨5470852932334811046401101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29177882305785658914139205 5470852932334811046401101)
                    ·
                      refine ⟨2051569849625554142400413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470852932334811046401101 2051569849625554142400413)
                      ·
                        rfl

theorem cell23_3995418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_3995418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995418 prefixEnd_3995418 := by exact prefixLift 3995418
  have htrace : WordTrace (prefixWord ++ tailWord_3995418) baseStart_3995418 baseEnd_3995418 := by
    simpa [prefixWord, tailWord_3995418, baseEnd_3995418] using wordTrace_append hprefix tailTrace_3995418
  have hstable : (prefixWord ++ tailWord_3995418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995418).length < 2 ^ (prefixWord ++ tailWord_3995418).sum := by decide
  have hdescent : baseEnd_3995418 < baseStart_3995418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995482 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3]
def baseStart_3995482 : Nat := 118140960795 + 3995482 * 2 ^ 59
def prefixEnd_3995482 : Nat := 4983230072969 + 3 ^ 40 * 3995482 * 2
def baseEnd_3995482 : Nat := 2051602712387441892000119

theorem tailTrace_3995482 : CollatzResearch.WordTrace tailWord_3995482 prefixEnd_3995482 2051602712387441892000119 := by
  unfold tailWord_3995482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36431800127764640711035175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97151467007372375229427133 36431800127764640711035175)
  ·
    refine ⟨54647700191646961066552763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36431800127764640711035175 54647700191646961066552763)
    ·
      refine ⟨81971550287470441599829145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54647700191646961066552763 81971550287470441599829145)
      ·
        refine ⟨61478662715602831199871859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81971550287470441599829145 61478662715602831199871859)
        ·
          refine ⟨92217994073404246799807789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61478662715602831199871859 92217994073404246799807789)
          ·
            refine ⟨34581747777526592549927921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92217994073404246799807789 34581747777526592549927921)
            ·
              refine ⟨25936310833144944412445941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34581747777526592549927921 25936310833144944412445941)
              ·
                refine ⟨2431529140607338538666807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25936310833144944412445941 2431529140607338538666807)
                ·
                  refine ⟨3647293710911007808000211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431529140607338538666807 3647293710911007808000211)
                  ·
                    refine ⟨5470940566366511712000317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3647293710911007808000211 5470940566366511712000317)
                    ·
                      refine ⟨2051602712387441892000119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470940566366511712000317 2051602712387441892000119)
                      ·
                        rfl

theorem cell23_3995482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_3995482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995482 prefixEnd_3995482 := by exact prefixLift 3995482
  have htrace : WordTrace (prefixWord ++ tailWord_3995482) baseStart_3995482 baseEnd_3995482 := by
    simpa [prefixWord, tailWord_3995482, baseEnd_3995482] using wordTrace_append hprefix tailTrace_3995482
  have hstable : (prefixWord ++ tailWord_3995482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995482).length < 2 ^ (prefixWord ++ tailWord_3995482).sum := by decide
  have hdescent : baseEnd_3995482 < baseStart_3995482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995525 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_3995525 : Nat := 118140960795 + 3995525 * 2 ^ 59
def prefixEnd_3995525 : Nat := 4983230072969 + 3 ^ 40 * 3995525 * 2
def baseEnd_3995525 : Nat := 2051624792055585223762421

theorem tailTrace_3995525 : CollatzResearch.WordTrace tailWord_3995525 prefixEnd_3995525 2051624792055585223762421 := by
  unfold tailWord_3995525
  simp only [CollatzResearch.WordTrace]
  refine ⟨145728768849902781187956029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97152512566601854125304019 145728768849902781187956029)
  ·
    refine ⟨54648288318713542945483511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145728768849902781187956029 54648288318713542945483511)
    ·
      refine ⟨81972432478070314418225267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54648288318713542945483511 81972432478070314418225267)
      ·
        refine ⟨122958648717105471627337901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81972432478070314418225267 122958648717105471627337901)
        ·
          refine ⟨46109493268914551860251713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122958648717105471627337901 46109493268914551860251713)
          ·
            refine ⟨34582119951685913895188785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46109493268914551860251713 34582119951685913895188785)
            ·
              refine ⟨25936589963764435421391589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34582119951685913895188785 25936589963764435421391589)
              ·
                refine ⟨4863110618205831641510923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25936589963764435421391589 4863110618205831641510923)
                ·
                  refine ⟨7294665927308747462266385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863110618205831641510923 7294665927308747462266385)
                  ·
                    refine ⟨5470999445481560596699789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7294665927308747462266385 5470999445481560596699789)
                    ·
                      refine ⟨2051624792055585223762421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5470999445481560596699789 2051624792055585223762421)
                      ·
                        rfl

theorem cell23_3995525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_3995525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995525 prefixEnd_3995525 := by exact prefixLift 3995525
  have htrace : WordTrace (prefixWord ++ tailWord_3995525) baseStart_3995525 baseEnd_3995525 := by
    simpa [prefixWord, tailWord_3995525, baseEnd_3995525] using wordTrace_append hprefix tailTrace_3995525
  have hstable : (prefixWord ++ tailWord_3995525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995525).length < 2 ^ (prefixWord ++ tailWord_3995525).sum := by decide
  have hdescent : baseEnd_3995525 < baseStart_3995525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995566 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3995566 : Nat := 118140960795 + 3995566 * 2 ^ 59
def prefixEnd_3995566 : Nat := 4983230072969 + 3 ^ 40 * 3995566 * 2
def baseEnd_3995566 : Nat := 683881948254139854449911

theorem tailTrace_3995566 : CollatzResearch.WordTrace tailWord_3995566 prefixEnd_3995566 683881948254139854449911 := by
  unfold tailWord_3995566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18216283030344280648774819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97153509495169496793465701 18216283030344280648774819)
  ·
    refine ⟨27324424545516420973162229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18216283030344280648774819 27324424545516420973162229)
    ·
      refine ⟨2561664801142164466233959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27324424545516420973162229 2561664801142164466233959)
      ·
        refine ⟨3842497201713246699350939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561664801142164466233959 3842497201713246699350939)
        ·
          refine ⟨5763745802569870049026409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842497201713246699350939 5763745802569870049026409)
          ·
            refine ⟨4322809351927402536769807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5763745802569870049026409 4322809351927402536769807)
            ·
              refine ⟨6484214027891103805154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322809351927402536769807 6484214027891103805154711)
              ·
                refine ⟨9726321041836655707732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484214027891103805154711 9726321041836655707732067)
                ·
                  refine ⟨14589481562754983561598101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9726321041836655707732067 14589481562754983561598101)
                  ·
                    refine ⟨683881948254139854449911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14589481562754983561598101 683881948254139854449911)
                    ·
                      rfl

theorem cell23_3995566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3995566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995566 prefixEnd_3995566 := by exact prefixLift 3995566
  have htrace : WordTrace (prefixWord ++ tailWord_3995566) baseStart_3995566 baseEnd_3995566 := by
    simpa [prefixWord, tailWord_3995566, baseEnd_3995566] using wordTrace_append hprefix tailTrace_3995566
  have hstable : (prefixWord ++ tailWord_3995566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995566).length < 2 ^ (prefixWord ++ tailWord_3995566).sum := by decide
  have hdescent : baseEnd_3995566 < baseStart_3995566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995595 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 3, 4, 2]
def baseStart_3995595 : Nat := 118140960795 + 3995595 * 2 ^ 59
def prefixEnd_3995595 : Nat := 4983230072969 + 3 ^ 40 * 3995595 * 2
def baseEnd_3995595 : Nat := 2051660735701399949887099

theorem tailTrace_3995595 : CollatzResearch.WordTrace tailWord_3995595 prefixEnd_3995595 2051660735701399949887099 := by
  unfold tailWord_3995595
  simp only [CollatzResearch.WordTrace]
  refine ⟨145731321959649183143004239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97154214639766122095336159 145731321959649183143004239)
  ·
    refine ⟨218596982939473774714506359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145731321959649183143004239 218596982939473774714506359)
    ·
      refine ⟨327895474409210662071759539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218596982939473774714506359 327895474409210662071759539)
      ·
        refine ⟨491843211613815993107639309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327895474409210662071759539 491843211613815993107639309)
        ·
          refine ⟨184441204355180997415364741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491843211613815993107639309 184441204355180997415364741)
          ·
            refine ⟨34582725816596437015380889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184441204355180997415364741 34582725816596437015380889)
            ·
              refine ⟨25937044362447327761535667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34582725816596437015380889 25937044362447327761535667)
              ·
                refine ⟨38905566543670991642303501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25937044362447327761535667 38905566543670991642303501)
                ·
                  refine ⟨14589587453876621865863813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38905566543670991642303501 14589587453876621865863813)
                  ·
                    refine ⟨2735547647601866599849465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14589587453876621865863813 2735547647601866599849465)
                    ·
                      refine ⟨2051660735701399949887099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735547647601866599849465 2051660735701399949887099)
                      ·
                        rfl

theorem cell23_3995595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4, 2].length) (baseStart_3995595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995595 prefixEnd_3995595 := by exact prefixLift 3995595
  have htrace : WordTrace (prefixWord ++ tailWord_3995595) baseStart_3995595 baseEnd_3995595 := by
    simpa [prefixWord, tailWord_3995595, baseEnd_3995595] using wordTrace_append hprefix tailTrace_3995595
  have hstable : (prefixWord ++ tailWord_3995595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995595).length < 2 ^ (prefixWord ++ tailWord_3995595).sum := by decide
  have hdescent : baseEnd_3995595 < baseStart_3995595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995623 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3995623 : Nat := 118140960795 + 3995623 * 2 ^ 59
def prefixEnd_3995623 : Nat := 4983230072969 + 3 ^ 40 * 3995623 * 2
def baseEnd_3995623 : Nat := 2051675113159725840336971

theorem tailTrace_3995623 : CollatzResearch.WordTrace tailWord_3995623 prefixEnd_3995623 2051675113159725840336971 := by
  unfold tailWord_3995623
  simp only [CollatzResearch.WordTrace]
  refine ⟨145732343203547743925023523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97154895469031829283349015 145732343203547743925023523)
  ·
    refine ⟨218598514805321615887535285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145732343203547743925023523 218598514805321615887535285)
    ·
      refine ⟨20493610762998901489456433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 218598514805321615887535285 20493610762998901489456433)
      ·
        refine ⟨15370208072249176117092325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20493610762998901489456433 15370208072249176117092325)
        ·
          refine ⟨2881914013546720521954811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15370208072249176117092325 2881914013546720521954811)
          ·
            refine ⟨4322871020320080782932217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881914013546720521954811 4322871020320080782932217)
            ·
              refine ⟨3242153265240060587199163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4322871020320080782932217 3242153265240060587199163)
              ·
                refine ⟨4863229897860090880798745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242153265240060587199163 4863229897860090880798745)
                ·
                  refine ⟨3647422423395068160599059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863229897860090880798745 3647422423395068160599059)
                  ·
                    refine ⟨5471133635092602240898589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3647422423395068160599059 5471133635092602240898589)
                    ·
                      refine ⟨2051675113159725840336971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5471133635092602240898589 2051675113159725840336971)
                      ·
                        rfl

theorem cell23_3995623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3995623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995623 prefixEnd_3995623 := by exact prefixLift 3995623
  have htrace : WordTrace (prefixWord ++ tailWord_3995623) baseStart_3995623 baseEnd_3995623 := by
    simpa [prefixWord, tailWord_3995623, baseEnd_3995623] using wordTrace_append hprefix tailTrace_3995623
  have hstable : (prefixWord ++ tailWord_3995623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995623).length < 2 ^ (prefixWord ++ tailWord_3995623).sum := by decide
  have hdescent : baseEnd_3995623 < baseStart_3995623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995702 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3995702 : Nat := 118140960795 + 3995702 * 2 ^ 59
def prefixEnd_3995702 : Nat := 4983230072969 + 3 ^ 40 * 3995702 * 2
def baseEnd_3995702 : Nat := 2051715678131431031249107

theorem tailTrace_3995702 : CollatzResearch.WordTrace tailWord_3995702 prefixEnd_3995702 2051715678131431031249107 := by
  unfold tailWord_3995702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108451535641346276071835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97156816380174360278099573 9108451535641346276071835)
  ·
    refine ⟨13662677303462019414107753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9108451535641346276071835 13662677303462019414107753)
    ·
      refine ⟨10247007977596514560580815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13662677303462019414107753 10247007977596514560580815)
      ·
        refine ⟨15370511966394771840871223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247007977596514560580815 15370511966394771840871223)
        ·
          refine ⟨23055767949592157761306835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15370511966394771840871223 23055767949592157761306835)
          ·
            refine ⟨34583651924388236641960253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23055767949592157761306835 34583651924388236641960253)
            ·
              refine ⟨12968869471645588740735095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34583651924388236641960253 12968869471645588740735095)
              ·
                refine ⟨19453304207468383111102643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12968869471645588740735095 19453304207468383111102643)
                ·
                  refine ⟨29179956311202574666653965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19453304207468383111102643 29179956311202574666653965)
                  ·
                    refine ⟨10942483616700965499995237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29179956311202574666653965 10942483616700965499995237)
                    ·
                      refine ⟨2051715678131431031249107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10942483616700965499995237 2051715678131431031249107)
                      ·
                        rfl

theorem cell23_3995702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3995702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995702 prefixEnd_3995702 := by exact prefixLift 3995702
  have htrace : WordTrace (prefixWord ++ tailWord_3995702) baseStart_3995702 baseEnd_3995702 := by
    simpa [prefixWord, tailWord_3995702, baseEnd_3995702] using wordTrace_append hprefix tailTrace_3995702
  have hstable : (prefixWord ++ tailWord_3995702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995702).length < 2 ^ (prefixWord ++ tailWord_3995702).sum := by decide
  have hdescent : baseEnd_3995702 < baseStart_3995702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995772 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_3995772 : Nat := 118140960795 + 3995772 * 2 ^ 59
def prefixEnd_3995772 : Nat := 4983230072969 + 3 ^ 40 * 3995772 * 2
def baseEnd_3995772 : Nat := 683917207259081919124595

theorem tailTrace_3995772 : CollatzResearch.WordTrace tailWord_3995772 prefixEnd_3995772 683917207259081919124595 := by
  unfold tailWord_3995772
  simp only [CollatzResearch.WordTrace]
  refine ⟨72868888840003971186098785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97158518453338628248131713 72868888840003971186098785)
  ·
    refine ⟨54651666630002978389574089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72868888840003971186098785 54651666630002978389574089)
    ·
      refine ⟨40988749972502233792180567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54651666630002978389574089 40988749972502233792180567)
      ·
        refine ⟨61483124958753350688270851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40988749972502233792180567 61483124958753350688270851)
        ·
          refine ⟨92224687438130026032406277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61483124958753350688270851 92224687438130026032406277)
          ·
            refine ⟨17292128894649379881076177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92224687438130026032406277 17292128894649379881076177)
            ·
              refine ⟨12969096670987034910807133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17292128894649379881076177 12969096670987034910807133)
              ·
                refine ⟨4863411251620138091552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12969096670987034910807133 4863411251620138091552675)
                ·
                  refine ⟨7295116877430207137329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863411251620138091552675 7295116877430207137329013)
                  ·
                    refine ⟨683917207259081919124595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7295116877430207137329013 683917207259081919124595)
                    ·
                      rfl

theorem cell23_3995772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_3995772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995772 prefixEnd_3995772 := by exact prefixLift 3995772
  have htrace : WordTrace (prefixWord ++ tailWord_3995772) baseStart_3995772 baseEnd_3995772 := by
    simpa [prefixWord, tailWord_3995772, baseEnd_3995772] using wordTrace_append hprefix tailTrace_3995772
  have hstable : (prefixWord ++ tailWord_3995772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995772).length < 2 ^ (prefixWord ++ tailWord_3995772).sum := by decide
  have hdescent : baseEnd_3995772 < baseStart_3995772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995779 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 2, 3, 2]
def baseStart_3995779 : Nat := 118140960795 + 3995779 * 2 ^ 59
def prefixEnd_3995779 : Nat := 4983230072969 + 3 ^ 40 * 3995779 * 2
def baseEnd_3995779 : Nat := 2051755216141827229986253

theorem tailTrace_3995779 : CollatzResearch.WordTrace tailWord_3995779 prefixEnd_3995779 2051755216141827229986253 := by
  unfold tailWord_3995779
  simp only [CollatzResearch.WordTrace]
  refine ⟨145738032990982582567702391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97158688660655055045134927 145738032990982582567702391)
  ·
    refine ⟨218607049486473873851553587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145738032990982582567702391 218607049486473873851553587)
    ·
      refine ⟨327910574229710810777330381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218607049486473873851553587 327910574229710810777330381)
      ·
        refine ⟨122966465336141554041498893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327910574229710810777330381 122966465336141554041498893)
        ·
          refine ⟨46112424501053082765562085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122966465336141554041498893 46112424501053082765562085)
          ·
            refine ⟨8646079593947453018542891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46112424501053082765562085 8646079593947453018542891)
            ·
              refine ⟨12969119390921179527814337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8646079593947453018542891 12969119390921179527814337)
              ·
                refine ⟨9726839543190884645860753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12969119390921179527814337 9726839543190884645860753)
                ·
                  refine ⟨7295129657393163484395565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9726839543190884645860753 7295129657393163484395565)
                  ·
                    refine ⟨2735673621522436306648337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7295129657393163484395565 2735673621522436306648337)
                    ·
                      refine ⟨2051755216141827229986253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735673621522436306648337 2051755216141827229986253)
                      ·
                        rfl

theorem cell23_3995779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_3995779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995779 prefixEnd_3995779 := by exact prefixLift 3995779
  have htrace : WordTrace (prefixWord ++ tailWord_3995779) baseStart_3995779 baseEnd_3995779 := by
    simpa [prefixWord, tailWord_3995779, baseEnd_3995779] using wordTrace_append hprefix tailTrace_3995779
  have hstable : (prefixWord ++ tailWord_3995779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995779).length < 2 ^ (prefixWord ++ tailWord_3995779).sum := by decide
  have hdescent : baseEnd_3995779 < baseStart_3995779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995786 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3995786 : Nat := 118140960795 + 3995786 * 2 ^ 59
def prefixEnd_3995786 : Nat := 4983230072969 + 3 ^ 40 * 3995786 * 2
def baseEnd_3995786 : Nat := 2051758810506408702598721

theorem tailTrace_3995786 : CollatzResearch.WordTrace tailWord_3995786 prefixEnd_3995786 2051758810506408702598721 := by
  unfold tailWord_3995786
  simp only [CollatzResearch.WordTrace]
  refine ⟨36434572075489305690801803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97158858867971481842138141 36434572075489305690801803)
  ·
    refine ⟨54651858113233958536202705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36434572075489305690801803 54651858113233958536202705)
    ·
      refine ⟨40988893584925468902152029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54651858113233958536202705 40988893584925468902152029)
      ·
        refine ⟨15370835094347050838307011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40988893584925468902152029 15370835094347050838307011)
        ·
          refine ⟨23056252641520576257460517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15370835094347050838307011 23056252641520576257460517)
          ·
            refine ⟨4323047370285108048273847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23056252641520576257460517 4323047370285108048273847)
            ·
              refine ⟨6484571055427662072410771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323047370285108048273847 6484571055427662072410771)
              ·
                refine ⟨9726856583141493108616157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484571055427662072410771 9726856583141493108616157)
                ·
                  refine ⟨3647571218678059915731059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9726856583141493108616157 3647571218678059915731059)
                  ·
                    refine ⟨5471356828017089873596589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3647571218678059915731059 5471356828017089873596589)
                    ·
                      refine ⟨2051758810506408702598721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5471356828017089873596589 2051758810506408702598721)
                      ·
                        rfl

theorem cell23_3995786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3995786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995786 prefixEnd_3995786 := by exact prefixLift 3995786
  have htrace : WordTrace (prefixWord ++ tailWord_3995786) baseStart_3995786 baseEnd_3995786 := by
    simpa [prefixWord, tailWord_3995786, baseEnd_3995786] using wordTrace_append hprefix tailTrace_3995786
  have hstable : (prefixWord ++ tailWord_3995786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995786).length < 2 ^ (prefixWord ++ tailWord_3995786).sum := by decide
  have hdescent : baseEnd_3995786 < baseStart_3995786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995795 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3]
def baseStart_3995795 : Nat := 118140960795 + 3995795 * 2 ^ 59
def prefixEnd_3995795 : Nat := 4983230072969 + 3 ^ 40 * 3995795 * 2
def baseEnd_3995795 : Nat := 2051763431832299167386179

theorem tailTrace_3995795 : CollatzResearch.WordTrace tailWord_3995795 prefixEnd_3995795 2051763431832299167386179 := by
  unfold tailWord_3995795
  simp only [CollatzResearch.WordTrace]
  refine ⟨145738616558924617300284839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97159077705949744866856559 145738616558924617300284839)
  ·
    refine ⟨218607924838386925950427259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145738616558924617300284839 218607924838386925950427259)
    ·
      refine ⟨327911887257580388925640889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218607924838386925950427259 327911887257580388925640889)
      ·
        refine ⟨245933915443185291694230667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327911887257580388925640889 245933915443185291694230667)
        ·
          refine ⟨368900873164777937541346001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245933915443185291694230667 368900873164777937541346001)
          ·
            refine ⟨276675654873583453156009501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368900873164777937541346001 276675654873583453156009501)
            ·
              refine ⟨103753370577593794933503563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276675654873583453156009501 103753370577593794933503563)
              ·
                refine ⟨155630055866390692400255345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103753370577593794933503563 155630055866390692400255345)
                ·
                  refine ⟨116722541899793019300191509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155630055866390692400255345 116722541899793019300191509)
                  ·
                    refine ⟨5471369151552797779696477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116722541899793019300191509 5471369151552797779696477)
                    ·
                      refine ⟨2051763431832299167386179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5471369151552797779696477 2051763431832299167386179)
                      ·
                        rfl

theorem cell23_3995795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_3995795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995795 prefixEnd_3995795 := by exact prefixLift 3995795
  have htrace : WordTrace (prefixWord ++ tailWord_3995795) baseStart_3995795 baseEnd_3995795 := by
    simpa [prefixWord, tailWord_3995795, baseEnd_3995795] using wordTrace_append hprefix tailTrace_3995795
  have hstable : (prefixWord ++ tailWord_3995795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995795).length < 2 ^ (prefixWord ++ tailWord_3995795).sum := by decide
  have hdescent : baseEnd_3995795 < baseStart_3995795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995809 : List Nat := [1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3995809 : Nat := 118140960795 + 3995809 * 2 ^ 59
def prefixEnd_3995809 : Nat := 4983230072969 + 3 ^ 40 * 3995809 * 2
def baseEnd_3995809 : Nat := 2051770620561462112611115

theorem tailTrace_3995809 : CollatzResearch.WordTrace tailWord_3995809 prefixEnd_3995809 2051770620561462112611115 := by
  unfold tailWord_3995809
  simp only [CollatzResearch.WordTrace]
  refine ⟨145739127180873897691294481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97159418120582598460862987 145739127180873897691294481)
  ·
    refine ⟨109304345385655423268470861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145739127180873897691294481 109304345385655423268470861)
    ·
      refine ⟨40989129519620783725676573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109304345385655423268470861 40989129519620783725676573)
      ·
        refine ⟨15370923569857793897128715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40989129519620783725676573 15370923569857793897128715)
        ·
          refine ⟨23056385354786690845693073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15370923569857793897128715 23056385354786690845693073)
          ·
            refine ⟨17292289016090018134269805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23056385354786690845693073 17292289016090018134269805)
            ·
              refine ⟨6484608381033756800351177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17292289016090018134269805 6484608381033756800351177)
              ·
                refine ⟨4863456285775317600263383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6484608381033756800351177 4863456285775317600263383)
                ·
                  refine ⟨7295184428662976400395075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4863456285775317600263383 7295184428662976400395075)
                  ·
                    refine ⟨10942776642994464600592613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7295184428662976400395075 10942776642994464600592613)
                    ·
                      refine ⟨2051770620561462112611115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10942776642994464600592613 2051770620561462112611115)
                      ·
                        rfl

theorem cell23_3995809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3995809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995809 prefixEnd_3995809 := by exact prefixLift 3995809
  have htrace : WordTrace (prefixWord ++ tailWord_3995809) baseStart_3995809 baseEnd_3995809 := by
    simpa [prefixWord, tailWord_3995809, baseEnd_3995809] using wordTrace_append hprefix tailTrace_3995809
  have hstable : (prefixWord ++ tailWord_3995809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995809).length < 2 ^ (prefixWord ++ tailWord_3995809).sum := by decide
  have hdescent : baseEnd_3995809 < baseStart_3995809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995836 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_3995836 : Nat := 118140960795 + 3995836 * 2 ^ 59
def prefixEnd_3995836 : Nat := 4983230072969 + 3 ^ 40 * 3995836 * 2
def baseEnd_3995836 : Nat := 683928161513044502324497

theorem tailTrace_3995836 : CollatzResearch.WordTrace tailWord_3995836 prefixEnd_3995836 683928161513044502324497 := by
  unfold tailWord_3995836
  simp only [CollatzResearch.WordTrace]
  refine ⟨72870055975888040651263681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97160074634517387535018241 72870055975888040651263681)
  ·
    refine ⟨54652541981916030488447761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72870055975888040651263681 54652541981916030488447761)
    ·
      refine ⟨40989406486437022866335821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54652541981916030488447761 40989406486437022866335821)
      ·
        refine ⟨15371027432413883574875933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40989406486437022866335821 15371027432413883574875933)
        ·
          refine ⟨5764135287155206340578475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15371027432413883574875933 5764135287155206340578475)
          ·
            refine ⟨8646202930732809510867713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764135287155206340578475 8646202930732809510867713)
            ·
              refine ⟨6484652198049607133150785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8646202930732809510867713 6484652198049607133150785)
              ·
                refine ⟨4863489148537205349863089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6484652198049607133150785 4863489148537205349863089)
                ·
                  refine ⟨3647616861402904012397317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4863489148537205349863089 3647616861402904012397317)
                  ·
                    refine ⟨683928161513044502324497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3647616861402904012397317 683928161513044502324497)
                    ·
                      rfl

theorem cell23_3995836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_3995836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995836 prefixEnd_3995836 := by exact prefixLift 3995836
  have htrace : WordTrace (prefixWord ++ tailWord_3995836) baseStart_3995836 baseEnd_3995836 := by
    simpa [prefixWord, tailWord_3995836, baseEnd_3995836] using wordTrace_append hprefix tailTrace_3995836
  have hstable : (prefixWord ++ tailWord_3995836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995836).length < 2 ^ (prefixWord ++ tailWord_3995836).sum := by decide
  have hdescent : baseEnd_3995836 < baseStart_3995836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995845 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_3995845 : Nat := 118140960795 + 3995845 * 2 ^ 59
def prefixEnd_3995845 : Nat := 4983230072969 + 3 ^ 40 * 3995845 * 2
def baseEnd_3995845 : Nat := 683929701955007990586983

theorem tailTrace_3995845 : CollatzResearch.WordTrace tailWord_3995845 prefixEnd_3995845 683929701955007990586983 := by
  unfold tailWord_3995845
  simp only [CollatzResearch.WordTrace]
  refine ⟨145740440208743475839604989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97160293472495650559736659 145740440208743475839604989)
  ·
    refine ⟨54652665078278803439851871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145740440208743475839604989 54652665078278803439851871)
    ·
      refine ⟨81978997617418205159777807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54652665078278803439851871 81978997617418205159777807)
      ·
        refine ⟨122968496426127307739666711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81978997617418205159777807 122968496426127307739666711)
        ·
          refine ⟨184452744639190961609500067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122968496426127307739666711 184452744639190961609500067)
          ·
            refine ⟨276679116958786442414250101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184452744639190961609500067 276679116958786442414250101)
            ·
              refine ⟨25938667214886228976335947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276679116958786442414250101 25938667214886228976335947)
              ·
                refine ⟨38908000822329343464503921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25938667214886228976335947 38908000822329343464503921)
                ·
                  refine ⟨29181000616747007598377941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38908000822329343464503921 29181000616747007598377941)
                  ·
                    refine ⟨683929701955007990586983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29181000616747007598377941 683929701955007990586983)
                    ·
                      rfl

theorem cell23_3995845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_3995845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995845 prefixEnd_3995845 := by exact prefixLift 3995845
  have htrace : WordTrace (prefixWord ++ tailWord_3995845) baseStart_3995845 baseEnd_3995845 := by
    simpa [prefixWord, tailWord_3995845, baseEnd_3995845] using wordTrace_append hprefix tailTrace_3995845
  have hstable : (prefixWord ++ tailWord_3995845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995845).length < 2 ^ (prefixWord ++ tailWord_3995845).sum := by decide
  have hdescent : baseEnd_3995845 < baseStart_3995845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995895 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_3995895 : Nat := 118140960795 + 3995895 * 2 ^ 59
def prefixEnd_3995895 : Nat := 4983230072969 + 3 ^ 40 * 3995895 * 2
def baseEnd_3995895 : Nat := 2051814779897748776135719

theorem tailTrace_3995895 : CollatzResearch.WordTrace tailWord_3995895 prefixEnd_3995895 2051814779897748776135719 := by
  unfold tailWord_3995895
  simp only [CollatzResearch.WordTrace]
  refine ⟨145742263858562334378925139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97161509239041556252616759 145742263858562334378925139)
  ·
    refine ⟨218613395787843501568387709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145742263858562334378925139 218613395787843501568387709)
    ·
      refine ⟨81980023420441313088145391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218613395787843501568387709 81980023420441313088145391)
      ·
        refine ⟨122970035130661969632218087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81980023420441313088145391 122970035130661969632218087)
        ·
          refine ⟨184455052695992954448327131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122970035130661969632218087 184455052695992954448327131)
          ·
            refine ⟨276682579043989431672490697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184455052695992954448327131 276682579043989431672490697)
            ·
              refine ⟨207511934282992073754368023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276682579043989431672490697 207511934282992073754368023)
              ·
                refine ⟨311267901424488110631552035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207511934282992073754368023 311267901424488110631552035)
                ·
                  refine ⟨466901852136732165947328053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311267901424488110631552035 466901852136732165947328053)
                  ·
                    refine ⟨43772048637818640557562005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 466901852136732165947328053 43772048637818640557562005)
                    ·
                      refine ⟨2051814779897748776135719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43772048637818640557562005 2051814779897748776135719)
                      ·
                        rfl

theorem cell23_3995895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_3995895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995895 prefixEnd_3995895 := by exact prefixLift 3995895
  have htrace : WordTrace (prefixWord ++ tailWord_3995895) baseStart_3995895 baseEnd_3995895 := by
    simpa [prefixWord, tailWord_3995895, baseEnd_3995895] using wordTrace_append hprefix tailTrace_3995895
  have hstable : (prefixWord ++ tailWord_3995895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995895).length < 2 ^ (prefixWord ++ tailWord_3995895).sum := by decide
  have hdescent : baseEnd_3995895 < baseStart_3995895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995956 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3995956 : Nat := 118140960795 + 3995956 * 2 ^ 59
def prefixEnd_3995956 : Nat := 4983230072969 + 3 ^ 40 * 3995956 * 2
def baseEnd_3995956 : Nat := 227982900246408115274771

theorem tailTrace_3995956 : CollatzResearch.WordTrace tailWord_3995956 prefixEnd_3995956 227982900246408115274771 := by
  unfold tailWord_3995956
  simp only [CollatzResearch.WordTrace]
  refine ⟨72872244355670670898447861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97162992474227561197930481 72872244355670670898447861)
  ·
    refine ⟨6831772908344125396729487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72872244355670670898447861 6831772908344125396729487)
    ·
      refine ⟨10247659362516188095094231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6831772908344125396729487 10247659362516188095094231)
      ·
        refine ⟨15371489043774282142641347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10247659362516188095094231 15371489043774282142641347)
        ·
          refine ⟨23057233565661423213962021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15371489043774282142641347 23057233565661423213962021)
          ·
            refine ⟨4323231293561516852617879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23057233565661423213962021 4323231293561516852617879)
            ·
              refine ⟨6484846940342275278926819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323231293561516852617879 6484846940342275278926819)
              ·
                refine ⟨9727270410513412918390229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6484846940342275278926819 9727270410513412918390229)
                ·
                  refine ⟨227982900246408115274771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9727270410513412918390229 227982900246408115274771)
                  ·
                    rfl

theorem cell23_3995956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3995956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995956 prefixEnd_3995956 := by exact prefixLift 3995956
  have htrace : WordTrace (prefixWord ++ tailWord_3995956) baseStart_3995956 baseEnd_3995956 := by
    simpa [prefixWord, tailWord_3995956, baseEnd_3995956] using wordTrace_append hprefix tailTrace_3995956
  have hstable : (prefixWord ++ tailWord_3995956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995956).length < 2 ^ (prefixWord ++ tailWord_3995956).sum := by decide
  have hdescent : baseEnd_3995956 < baseStart_3995956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3995962 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_3995962 : Nat := 118140960795 + 3995962 * 2 ^ 59
def prefixEnd_3995962 : Nat := 4983230072969 + 3 ^ 40 * 3995962 * 2
def baseEnd_3995962 : Nat := 2051849183101600013997911

theorem tailTrace_3995962 : CollatzResearch.WordTrace tailWord_3995962 prefixEnd_3995962 2051849183101600013997911 := by
  unfold tailWord_3995962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36436176887329901205403535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97163138366213069881076093 36436176887329901205403535)
  ·
    refine ⟨54654265330994851808105303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36436176887329901205403535 54654265330994851808105303)
    ·
      refine ⟨81981397996492277712157955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54654265330994851808105303 81981397996492277712157955)
      ·
        refine ⟨122972096994738416568236933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81981397996492277712157955 122972096994738416568236933)
        ·
          refine ⟨23057268186513453106544425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122972096994738416568236933 23057268186513453106544425)
          ·
            refine ⟨17292951139885089829908319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23057268186513453106544425 17292951139885089829908319)
            ·
              refine ⟨25939426709827634744862479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17292951139885089829908319 25939426709827634744862479)
              ·
                refine ⟨38909140064741452117293719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25939426709827634744862479 38909140064741452117293719)
                ·
                  refine ⟨58363710097112178175940579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38909140064741452117293719 58363710097112178175940579)
                  ·
                    refine ⟨87545565145668267263910869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58363710097112178175940579 87545565145668267263910869)
                    ·
                      refine ⟨2051849183101600013997911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 87545565145668267263910869 2051849183101600013997911)
                      ·
                        rfl

theorem cell23_3995962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_3995962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3995962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3995962 prefixEnd_3995962 := by exact prefixLift 3995962
  have htrace : WordTrace (prefixWord ++ tailWord_3995962) baseStart_3995962 baseEnd_3995962 := by
    simpa [prefixWord, tailWord_3995962, baseEnd_3995962] using wordTrace_append hprefix tailTrace_3995962
  have hstable : (prefixWord ++ tailWord_3995962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3995962).length < 2 ^ (prefixWord ++ tailWord_3995962).sum := by decide
  have hdescent : baseEnd_3995962 < baseStart_3995962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3995962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996009 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_3996009 : Nat := 118140960795 + 3996009 * 2 ^ 59
def prefixEnd_3996009 : Nat := 4983230072969 + 3 ^ 40 * 3996009 * 2
def baseEnd_3996009 : Nat := 2051873316692361330110195

theorem tailTrace_3996009 : CollatzResearch.WordTrace tailWord_3996009 prefixEnd_3996009 2051873316692361330110195 := by
  unfold tailWord_3996009
  simp only [CollatzResearch.WordTrace]
  refine ⟨145746421780149331848575081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97164281186766221232383387 145746421780149331848575081)
  ·
    refine ⟨109309816335111998886431311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145746421780149331848575081 109309816335111998886431311)
    ·
      refine ⟨163964724502667998329646967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109309816335111998886431311 163964724502667998329646967)
      ·
        refine ⟨245947086754001997494470451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163964724502667998329646967 245947086754001997494470451)
        ·
          refine ⟨368920630131002996241705677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245947086754001997494470451 368920630131002996241705677)
          ·
            refine ⟨138345236299126123590639629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 368920630131002996241705677 138345236299126123590639629)
            ·
              refine ⟨51879463612172296346489861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138345236299126123590639629 51879463612172296346489861)
              ·
                refine ⟨9727399427282305564966849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51879463612172296346489861 9727399427282305564966849)
                ·
                  refine ⟨7295549570461729173725137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9727399427282305564966849 7295549570461729173725137)
                  ·
                    refine ⟨5471662177846296880293853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7295549570461729173725137 5471662177846296880293853)
                    ·
                      refine ⟨2051873316692361330110195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5471662177846296880293853 2051873316692361330110195)
                      ·
                        rfl

theorem cell23_3996009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_3996009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996009 prefixEnd_3996009 := by exact prefixLift 3996009
  have htrace : WordTrace (prefixWord ++ tailWord_3996009) baseStart_3996009 baseEnd_3996009 := by
    simpa [prefixWord, tailWord_3996009, baseEnd_3996009] using wordTrace_append hprefix tailTrace_3996009
  have hstable : (prefixWord ++ tailWord_3996009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996009).length < 2 ^ (prefixWord ++ tailWord_3996009).sum := by decide
  have hdescent : baseEnd_3996009 < baseStart_3996009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996029 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 6]
def baseStart_3996029 : Nat := 118140960795 + 3996029 * 2 ^ 59
def prefixEnd_3996029 : Nat := 4983230072969 + 3 ^ 40 * 3996029 * 2
def baseEnd_3996029 : Nat := 227987065145050139095567

theorem tailTrace_3996029 : CollatzResearch.WordTrace tailWord_3996029 prefixEnd_3996029 227987065145050139095567 := by
  unfold tailWord_3996029
  simp only [CollatzResearch.WordTrace]
  refine ⟨145747151240076875264303141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97164767493384583509535427 145747151240076875264303141)
  ·
    refine ⟨27327590857514414112056839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145747151240076875264303141 27327590857514414112056839)
    ·
      refine ⟨40991386286271621168085259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27327590857514414112056839 40991386286271621168085259)
      ·
        refine ⟨61487079429407431752127889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40991386286271621168085259 61487079429407431752127889)
        ·
          refine ⟨46115309572055573814095917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61487079429407431752127889 46115309572055573814095917)
          ·
            refine ⟨17293241089520840180285969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46115309572055573814095917 17293241089520840180285969)
            ·
              refine ⟨12969930817140630135214477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17293241089520840180285969 12969930817140630135214477)
              ·
                refine ⟨4863724056427736300705429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12969930817140630135214477 4863724056427736300705429)
                ·
                  refine ⟨227987065145050139095567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4863724056427736300705429 227987065145050139095567)
                  ·
                    rfl

theorem cell23_3996029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_3996029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996029 prefixEnd_3996029 := by exact prefixLift 3996029
  have htrace : WordTrace (prefixWord ++ tailWord_3996029) baseStart_3996029 baseEnd_3996029 := by
    simpa [prefixWord, tailWord_3996029, baseEnd_3996029] using wordTrace_append hprefix tailTrace_3996029
  have hstable : (prefixWord ++ tailWord_3996029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996029).length < 2 ^ (prefixWord ++ tailWord_3996029).sum := by decide
  have hdescent : baseEnd_3996029 < baseStart_3996029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996116 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3996116 : Nat := 118140960795 + 3996116 * 2 ^ 59
def prefixEnd_3996116 : Nat := 4983230072969 + 3 ^ 40 * 3996116 * 2
def baseEnd_3996116 : Nat := 2051928259122392411472203

theorem tailTrace_3996116 : CollatzResearch.WordTrace tailWord_3996116 prefixEnd_3996116 2051928259122392411472203 := by
  unfold tailWord_3996116
  simp only [CollatzResearch.WordTrace]
  refine ⟨72875162195380844561360101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97166882927174459415146801 72875162195380844561360101)
  ·
    refine ⟨13664092911633908355255019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72875162195380844561360101 13664092911633908355255019)
    ·
      refine ⟨20496139367450862532882529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13664092911633908355255019 20496139367450862532882529)
      ·
        refine ⟨15372104525588146899661897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20496139367450862532882529 15372104525588146899661897)
        ·
          refine ⟨11529078394191110174746423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15372104525588146899661897 11529078394191110174746423)
          ·
            refine ⟨17293617591286665262119635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529078394191110174746423 17293617591286665262119635)
            ·
              refine ⟨25940426386929997893179453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17293617591286665262119635 25940426386929997893179453)
              ·
                refine ⟨9727659895098749209942295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25940426386929997893179453 9727659895098749209942295)
                ·
                  refine ⟨14591489842648123814913443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9727659895098749209942295 14591489842648123814913443)
                  ·
                    refine ⟨21887234763972185722370165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14591489842648123814913443 21887234763972185722370165)
                    ·
                      refine ⟨2051928259122392411472203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21887234763972185722370165 2051928259122392411472203)
                      ·
                        rfl

theorem cell23_3996116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3996116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996116 prefixEnd_3996116 := by exact prefixLift 3996116
  have htrace : WordTrace (prefixWord ++ tailWord_3996116) baseStart_3996116 baseEnd_3996116 := by
    simpa [prefixWord, tailWord_3996116, baseEnd_3996116] using wordTrace_append hprefix tailTrace_3996116
  have hstable : (prefixWord ++ tailWord_3996116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996116).length < 2 ^ (prefixWord ++ tailWord_3996116).sum := by decide
  have hdescent : baseEnd_3996116 < baseStart_3996116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996179 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 2, 6]
def baseStart_3996179 : Nat := 118140960795 + 3996179 * 2 ^ 59
def prefixEnd_3996179 : Nat := 4983230072969 + 3 ^ 40 * 3996179 * 2
def baseEnd_3996179 : Nat := 683986869467875221661471

theorem tailTrace_3996179 : CollatzResearch.WordTrace tailWord_3996179 prefixEnd_3996179 683986869467875221661471 := by
  unfold tailWord_3996179
  simp only [CollatzResearch.WordTrace]
  refine ⟨145752622189533450882263591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97168414793022300588175727 145752622189533450882263591)
  ·
    refine ⟨218628933284300176323395387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145752622189533450882263591 218628933284300176323395387)
    ·
      refine ⟨327943399926450264485093081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218628933284300176323395387 327943399926450264485093081)
      ·
        refine ⟨245957549944837698363819811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327943399926450264485093081 245957549944837698363819811)
        ·
          refine ⟨368936324917256547545729717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245957549944837698363819811 368936324917256547545729717)
          ·
            refine ⟨34587780460992801332412161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 368936324917256547545729717 34587780460992801332412161)
            ·
              refine ⟨25940835345744600999309121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34587780460992801332412161 25940835345744600999309121)
              ·
                refine ⟨19455626509308450749481841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25940835345744600999309121 19455626509308450749481841)
                ·
                  refine ⟨14591719881981338062111381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19455626509308450749481841 14591719881981338062111381)
                  ·
                    refine ⟨683986869467875221661471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14591719881981338062111381 683986869467875221661471)
                    ·
                      rfl

theorem cell23_3996179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 6].length) (baseStart_3996179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996179 prefixEnd_3996179 := by exact prefixLift 3996179
  have htrace : WordTrace (prefixWord ++ tailWord_3996179) baseStart_3996179 baseEnd_3996179 := by
    simpa [prefixWord, tailWord_3996179, baseEnd_3996179] using wordTrace_append hprefix tailTrace_3996179
  have hstable : (prefixWord ++ tailWord_3996179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996179).length < 2 ^ (prefixWord ++ tailWord_3996179).sum := by decide
  have hdescent : baseEnd_3996179 < baseStart_3996179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996209 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 9]
def baseStart_3996209 : Nat := 118140960795 + 3996209 * 2 ^ 59
def prefixEnd_3996209 : Nat := 4983230072969 + 3 ^ 40 * 3996209 * 2
def baseEnd_3996209 : Nat := 227997334758140060845475

theorem tailTrace_3996209 : CollatzResearch.WordTrace tailWord_3996209 prefixEnd_3996209 227997334758140060845475 := by
  unfold tailWord_3996209
  simp only [CollatzResearch.WordTrace]
  refine ⟨145753716379424766005855681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97169144252949844003903787 145753716379424766005855681)
  ·
    refine ⟨109315287284568574504391761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145753716379424766005855681 109315287284568574504391761)
    ·
      refine ⟨81986465463426430878293821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109315287284568574504391761 81986465463426430878293821)
      ·
        refine ⟨30744924548784911579360183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81986465463426430878293821 30744924548784911579360183)
        ·
          refine ⟨46117386823177367369040275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30744924548784911579360183 46117386823177367369040275)
          ·
            refine ⟨69176080234766051053560413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46117386823177367369040275 69176080234766051053560413)
            ·
              refine ⟨25941030088037269145085155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69176080234766051053560413 25941030088037269145085155)
              ·
                refine ⟨38911545132055903717627733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25941030088037269145085155 38911545132055903717627733)
                ·
                  refine ⟨227997334758140060845475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38911545132055903717627733 227997334758140060845475)
                  ·
                    rfl

theorem cell23_3996209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_3996209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996209 prefixEnd_3996209 := by exact prefixLift 3996209
  have htrace : WordTrace (prefixWord ++ tailWord_3996209) baseStart_3996209 baseEnd_3996209 := by
    simpa [prefixWord, tailWord_3996209, baseEnd_3996209] using wordTrace_append hprefix tailTrace_3996209
  have hstable : (prefixWord ++ tailWord_3996209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996209).length < 2 ^ (prefixWord ++ tailWord_3996209).sum := by decide
  have hdescent : baseEnd_3996209 < baseStart_3996209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996236 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3996236 : Nat := 118140960795 + 3996236 * 2 ^ 59
def prefixEnd_3996236 : Nat := 4983230072969 + 3 ^ 40 * 3996236 * 2
def baseEnd_3996236 : Nat := 2051989876800931941971651

theorem tailTrace_3996236 : CollatzResearch.WordTrace tailWord_3996236 prefixEnd_3996236 2051989876800931941971651 := by
  unfold tailWord_3996236
  simp only [CollatzResearch.WordTrace]
  refine ⟨72877350575163474808544281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97169800766884633078059041 72877350575163474808544281)
  ·
    refine ⟨54658012931372606106408211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72877350575163474808544281 54658012931372606106408211)
    ·
      refine ⟨81987019397058909159612317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54658012931372606106408211 81987019397058909159612317)
      ·
        refine ⟨30745132273897090934854619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81987019397058909159612317 30745132273897090934854619)
        ·
          refine ⟨46117698410845636402281929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30745132273897090934854619 46117698410845636402281929)
          ·
            refine ⟨34588273808134227301711447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46117698410845636402281929 34588273808134227301711447)
            ·
              refine ⟨51882410712201340952567171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34588273808134227301711447 51882410712201340952567171)
              ·
                refine ⟨77823616068302011428850757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51882410712201340952567171 77823616068302011428850757)
                ·
                  refine ⟨14591928012806627142909517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77823616068302011428850757 14591928012806627142909517)
                  ·
                    refine ⟨5471973004802485178591069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14591928012806627142909517 5471973004802485178591069)
                    ·
                      refine ⟨2051989876800931941971651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5471973004802485178591069 2051989876800931941971651)
                      ·
                        rfl

theorem cell23_3996236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3996236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996236 prefixEnd_3996236 := by exact prefixLift 3996236
  have htrace : WordTrace (prefixWord ++ tailWord_3996236) baseStart_3996236 baseEnd_3996236 := by
    simpa [prefixWord, tailWord_3996236, baseEnd_3996236] using wordTrace_append hprefix tailTrace_3996236
  have hstable : (prefixWord ++ tailWord_3996236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996236).length < 2 ^ (prefixWord ++ tailWord_3996236).sum := by decide
  have hdescent : baseEnd_3996236 < baseStart_3996236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996237 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_3996237 : Nat := 118140960795 + 3996237 * 2 ^ 59
def prefixEnd_3996237 : Nat := 4983230072969 + 3 ^ 40 * 3996237 * 2
def baseEnd_3996237 : Nat := 2051990390281586438059147

theorem tailTrace_3996237 : CollatzResearch.WordTrace tailWord_3996237 prefixEnd_3996237 2051990390281586438059147 := by
  unfold tailWord_3996237
  simp only [CollatzResearch.WordTrace]
  refine ⟨145754737623323326787874965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97169825082215551191916643 145754737623323326787874965)
  ·
    refine ⟨6832253326093280943181639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145754737623323326787874965 6832253326093280943181639)
    ·
      refine ⟨10248379989139921414772459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6832253326093280943181639 10248379989139921414772459)
      ·
        refine ⟨15372569983709882122158689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10248379989139921414772459 15372569983709882122158689)
        ·
          refine ⟨11529427487782411591619017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15372569983709882122158689 11529427487782411591619017)
          ·
            refine ⟨8647070615836808693714263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11529427487782411591619017 8647070615836808693714263)
            ·
              refine ⟨12970605923755213040571395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8647070615836808693714263 12970605923755213040571395)
              ·
                refine ⟨19455908885632819560857093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12970605923755213040571395 19455908885632819560857093)
                ·
                  refine ⟨3647982916056153667660705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19455908885632819560857093 3647982916056153667660705)
                  ·
                    refine ⟨2735987187042115250745529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3647982916056153667660705 2735987187042115250745529)
                    ·
                      refine ⟨2051990390281586438059147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2735987187042115250745529 2051990390281586438059147)
                      ·
                        rfl

theorem cell23_3996237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_3996237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996237 prefixEnd_3996237 := by exact prefixLift 3996237
  have htrace : WordTrace (prefixWord ++ tailWord_3996237) baseStart_3996237 baseEnd_3996237 := by
    simpa [prefixWord, tailWord_3996237, baseEnd_3996237] using wordTrace_append hprefix tailTrace_3996237
  have hstable : (prefixWord ++ tailWord_3996237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996237).length < 2 ^ (prefixWord ++ tailWord_3996237).sum := by decide
  have hdescent : baseEnd_3996237 < baseStart_3996237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996277 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 5]
def baseStart_3996277 : Nat := 118140960795 + 3996277 * 2 ^ 59
def prefixEnd_3996277 : Nat := 4983230072969 + 3 ^ 40 * 3996277 * 2
def baseEnd_3996277 : Nat := 228001214389751809062107

theorem tailTrace_3996277 : CollatzResearch.WordTrace tailWord_3996277 prefixEnd_3996277 228001214389751809062107 := by
  unfold tailWord_3996277
  simp only [CollatzResearch.WordTrace]
  refine ⟨145756196543178413619331085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97170797695452275746220723 145756196543178413619331085)
  ·
    refine ⟨54658573703691905107249157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145756196543178413619331085 54658573703691905107249157)
    ·
      refine ⟨10248482569442232207609217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54658573703691905107249157 10248482569442232207609217)
      ·
        refine ⟨7686361927081674155706913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10248482569442232207609217 7686361927081674155706913)
        ·
          refine ⟨5764771445311255616780185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7686361927081674155706913 5764771445311255616780185)
          ·
            refine ⟨4323578583983441712585139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5764771445311255616780185 4323578583983441712585139)
            ·
              refine ⟨6485367875975162568877709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323578583983441712585139 6485367875975162568877709)
              ·
                refine ⟨2432012953490685963329141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6485367875975162568877709 2432012953490685963329141)
                ·
                  refine ⟨228001214389751809062107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2432012953490685963329141 228001214389751809062107)
                  ·
                    rfl

theorem cell23_3996277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_3996277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996277 prefixEnd_3996277 := by exact prefixLift 3996277
  have htrace : WordTrace (prefixWord ++ tailWord_3996277) baseStart_3996277 baseEnd_3996277 := by
    simpa [prefixWord, tailWord_3996277, baseEnd_3996277] using wordTrace_append hprefix tailTrace_3996277
  have hstable : (prefixWord ++ tailWord_3996277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996277).length < 2 ^ (prefixWord ++ tailWord_3996277).sum := by decide
  have hdescent : baseEnd_3996277 < baseStart_3996277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996293 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_3996293 : Nat := 118140960795 + 3996293 * 2 ^ 59
def prefixEnd_3996293 : Nat := 4983230072969 + 3 ^ 40 * 3996293 * 2
def baseEnd_3996293 : Nat := 2052019145198238218958889

theorem tailTrace_3996293 : CollatzResearch.WordTrace tailWord_3996293 prefixEnd_3996293 2052019145198238218958889 := by
  unfold tailWord_3996293
  simp only [CollatzResearch.WordTrace]
  refine ⟨145756780111120448351913533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97171186740746965567942355 145756780111120448351913533)
  ·
    refine ⟨54658792541670168131967575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145756780111120448351913533 54658792541670168131967575)
    ·
      refine ⟨81988188812505252197951363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54658792541670168131967575 81988188812505252197951363)
      ·
        refine ⟨122982283218757878296927045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81988188812505252197951363 122982283218757878296927045)
        ·
          refine ⟨23059178103517102180673821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122982283218757878296927045 23059178103517102180673821)
          ·
            refine ⟨8647191788818913317752683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23059178103517102180673821 8647191788818913317752683)
            ·
              refine ⟨12970787683228369976629025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8647191788818913317752683 12970787683228369976629025)
              ·
                refine ⟨9728090762421277482471769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12970787683228369976629025 9728090762421277482471769)
                ·
                  refine ⟨7296068071815958111853827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9728090762421277482471769 7296068071815958111853827)
                  ·
                    refine ⟨10944102107723937167780741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296068071815958111853827 10944102107723937167780741)
                    ·
                      refine ⟨2052019145198238218958889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10944102107723937167780741 2052019145198238218958889)
                      ·
                        rfl

theorem cell23_3996293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_3996293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996293 prefixEnd_3996293 := by exact prefixLift 3996293
  have htrace : WordTrace (prefixWord ++ tailWord_3996293) baseStart_3996293 baseEnd_3996293 := by
    simpa [prefixWord, tailWord_3996293, baseEnd_3996293] using wordTrace_append hprefix tailTrace_3996293
  have hstable : (prefixWord ++ tailWord_3996293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996293).length < 2 ^ (prefixWord ++ tailWord_3996293).sum := by decide
  have hdescent : baseEnd_3996293 < baseStart_3996293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996327 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3996327 : Nat := 118140960795 + 3996327 * 2 ^ 59
def prefixEnd_3996327 : Nat := 4983230072969 + 3 ^ 40 * 3996327 * 2
def baseEnd_3996327 : Nat := 2052036603540491085933733

theorem tailTrace_3996327 : CollatzResearch.WordTrace tailWord_3996327 prefixEnd_3996327 2052036603540491085933733 := by
  unfold tailWord_3996327
  simp only [CollatzResearch.WordTrace]
  refine ⟨145758020192997272158651235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97172013461998181439100823 145758020192997272158651235)
  ·
    refine ⟨218637030289495908237976853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145758020192997272158651235 218637030289495908237976853)
    ·
      refine ⟨10248610794820120698655165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 218637030289495908237976853 10248610794820120698655165)
      ·
        refine ⟨3843229048057545261995687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10248610794820120698655165 3843229048057545261995687)
        ·
          refine ⟨5764843572086317892993531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3843229048057545261995687 5764843572086317892993531)
          ·
            refine ⟨8647265358129476839490297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764843572086317892993531 8647265358129476839490297)
            ·
              refine ⟨6485449018597107629617723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8647265358129476839490297 6485449018597107629617723)
              ·
                refine ⟨9728173527895661444426585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485449018597107629617723 9728173527895661444426585)
                ·
                  refine ⟨7296130145921746083319939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9728173527895661444426585 7296130145921746083319939)
                  ·
                    refine ⟨10944195218882619124979909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296130145921746083319939 10944195218882619124979909)
                    ·
                      refine ⟨2052036603540491085933733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10944195218882619124979909 2052036603540491085933733)
                      ·
                        rfl

theorem cell23_3996327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3996327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996327 prefixEnd_3996327 := by exact prefixLift 3996327
  have htrace : WordTrace (prefixWord ++ tailWord_3996327) baseStart_3996327 baseEnd_3996327 := by
    simpa [prefixWord, tailWord_3996327, baseEnd_3996327] using wordTrace_append hprefix tailTrace_3996327
  have hstable : (prefixWord ++ tailWord_3996327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996327).length < 2 ^ (prefixWord ++ tailWord_3996327).sum := by decide
  have hdescent : baseEnd_3996327 < baseStart_3996327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996380 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3996380 : Nat := 118140960795 + 3996380 * 2 ^ 59
def prefixEnd_3996380 : Nat := 4983230072969 + 3 ^ 40 * 3996380 * 2
def baseEnd_3996380 : Nat := 684021272671726459523663

theorem tailTrace_3996380 : CollatzResearch.WordTrace tailWord_3996380 prefixEnd_3996380 684021272671726459523663 := by
  unfold tailWord_3996380
  simp only [CollatzResearch.WordTrace]
  refine ⟨72879976630902631105165297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97173302174536841473553729 72879976630902631105165297)
  ·
    refine ⟨54659982473176973328873973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72879976630902631105165297 54659982473176973328873973)
    ·
      refine ⟨5124373356860341249581935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54659982473176973328873973 5124373356860341249581935)
      ·
        refine ⟨7686560035290511874372903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124373356860341249581935 7686560035290511874372903)
        ·
          refine ⟨11529840052935767811559355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686560035290511874372903 11529840052935767811559355)
          ·
            refine ⟨17294760079403651717339033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529840052935767811559355 17294760079403651717339033)
            ·
              refine ⟨12971070059552738788004275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17294760079403651717339033 12971070059552738788004275)
              ·
                refine ⟨19456605089329108182006413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12971070059552738788004275 19456605089329108182006413)
                ·
                  refine ⟨7296226908498415568252405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19456605089329108182006413 7296226908498415568252405)
                  ·
                    refine ⟨684021272671726459523663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296226908498415568252405 684021272671726459523663)
                    ·
                      rfl

theorem cell23_3996380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3996380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996380 prefixEnd_3996380 := by exact prefixLift 3996380
  have htrace : WordTrace (prefixWord ++ tailWord_3996380) baseStart_3996380 baseEnd_3996380 := by
    simpa [prefixWord, tailWord_3996380, baseEnd_3996380] using wordTrace_append hprefix tailTrace_3996380
  have hstable : (prefixWord ++ tailWord_3996380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996380).length < 2 ^ (prefixWord ++ tailWord_3996380).sum := by decide
  have hdescent : baseEnd_3996380 < baseStart_3996380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996383 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_3996383 : Nat := 118140960795 + 3996383 * 2 ^ 59
def prefixEnd_3996383 : Nat := 4983230072969 + 3 ^ 40 * 3996383 * 2
def baseEnd_3996383 : Nat := 2052065358457142866833475

theorem tailTrace_3996383 : CollatzResearch.WordTrace tailWord_3996383 prefixEnd_3996383 2052065358457142866833475 := by
  unfold tailWord_3996383
  simp only [CollatzResearch.WordTrace]
  refine ⟨145760062680794393722689803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97173375120529595815126535 145760062680794393722689803)
  ·
    refine ⟨218640094021191590584034705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145760062680794393722689803 218640094021191590584034705)
    ·
      refine ⟨163980070515893692938026029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218640094021191590584034705 163980070515893692938026029)
      ·
        refine ⟨61492526443460134851759761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163980070515893692938026029 61492526443460134851759761)
        ·
          refine ⟨46119394832595101138819821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61492526443460134851759761 46119394832595101138819821)
          ·
            refine ⟨17294773062223162927057433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46119394832595101138819821 17294773062223162927057433)
            ·
              refine ⟨12971079796667372195293075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17294773062223162927057433 12971079796667372195293075)
              ·
                refine ⟨19456619695001058292939613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12971079796667372195293075 19456619695001058292939613)
                ·
                  refine ⟨7296232385625396859852355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19456619695001058292939613 7296232385625396859852355)
                  ·
                    refine ⟨10944348578438095289778533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296232385625396859852355 10944348578438095289778533)
                    ·
                      refine ⟨2052065358457142866833475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10944348578438095289778533 2052065358457142866833475)
                      ·
                        rfl

theorem cell23_3996383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_3996383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996383 prefixEnd_3996383 := by exact prefixLift 3996383
  have htrace : WordTrace (prefixWord ++ tailWord_3996383) baseStart_3996383 baseEnd_3996383 := by
    simpa [prefixWord, tailWord_3996383, baseEnd_3996383] using wordTrace_append hprefix tailTrace_3996383
  have hstable : (prefixWord ++ tailWord_3996383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996383).length < 2 ^ (prefixWord ++ tailWord_3996383).sum := by decide
  have hdescent : baseEnd_3996383 < baseStart_3996383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996387 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3996387 : Nat := 118140960795 + 3996387 * 2 ^ 59
def prefixEnd_3996387 : Nat := 4983230072969 + 3 ^ 40 * 3996387 * 2
def baseEnd_3996387 : Nat := 2052067412379760851183457

theorem tailTrace_3996387 : CollatzResearch.WordTrace tailWord_3996387 prefixEnd_3996387 2052067412379760851183457 := by
  unfold tailWord_3996387
  simp only [CollatzResearch.WordTrace]
  refine ⟨145760208572779902405835415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97173472381853268270556943 145760208572779902405835415)
  ·
    refine ⟨218640312859169853608753123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145760208572779902405835415 218640312859169853608753123)
    ·
      refine ⟨327960469288754780413129685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218640312859169853608753123 327960469288754780413129685)
      ·
        refine ⟨7686573498955190165932727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 327960469288754780413129685 7686573498955190165932727)
        ·
          refine ⟨11529860248432785248899091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7686573498955190165932727 11529860248432785248899091)
          ·
            refine ⟨17294790372649177873348637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11529860248432785248899091 17294790372649177873348637)
            ·
              refine ⟨6485546389743441702505739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17294790372649177873348637 6485546389743441702505739)
              ·
                refine ⟨9728319584615162553758609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485546389743441702505739 9728319584615162553758609)
                ·
                  refine ⟨7296239688461371915318957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9728319584615162553758609 7296239688461371915318957)
                  ·
                    refine ⟨2736089883173014468244609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7296239688461371915318957 2736089883173014468244609)
                    ·
                      refine ⟨2052067412379760851183457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736089883173014468244609 2052067412379760851183457)
                      ·
                        rfl

theorem cell23_3996387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3996387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996387 prefixEnd_3996387 := by exact prefixLift 3996387
  have htrace : WordTrace (prefixWord ++ tailWord_3996387) baseStart_3996387 baseEnd_3996387 := by
    simpa [prefixWord, tailWord_3996387, baseEnd_3996387] using wordTrace_append hprefix tailTrace_3996387
  have hstable : (prefixWord ++ tailWord_3996387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996387).length < 2 ^ (prefixWord ++ tailWord_3996387).sum := by decide
  have hdescent : baseEnd_3996387 < baseStart_3996387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996396 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_3996396 : Nat := 118140960795 + 3996396 * 2 ^ 59
def prefixEnd_3996396 : Nat := 4983230072969 + 3 ^ 40 * 3996396 * 2
def baseEnd_3996396 : Nat := 2052072033705651315970915

theorem tailTrace_3996396 : CollatzResearch.WordTrace tailWord_3996396 prefixEnd_3996396 2052072033705651315970915 := by
  unfold tailWord_3996396
  simp only [CollatzResearch.WordTrace]
  refine ⟨72880268414873648471456521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97173691219831531295275361 72880268414873648471456521)
  ·
    refine ⟨54660201311155236353592391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72880268414873648471456521 54660201311155236353592391)
    ·
      refine ⟨81990301966732854530388587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54660201311155236353592391 81990301966732854530388587)
      ·
        refine ⟨122985452950099281795582881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81990301966732854530388587 122985452950099281795582881)
        ·
          refine ⟨92239089712574461346687161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122985452950099281795582881 92239089712574461346687161)
          ·
            refine ⟨69179317284430846010015371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92239089712574461346687161 69179317284430846010015371)
            ·
              refine ⟨103768975926646269015023057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69179317284430846010015371 103768975926646269015023057)
              ·
                refine ⟨77826731944984701761267293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103768975926646269015023057 77826731944984701761267293)
                ·
                  refine ⟨29185024479369263160475235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77826731944984701761267293 29185024479369263160475235)
                  ·
                    refine ⟨43777536719053894740712853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29185024479369263160475235 43777536719053894740712853)
                    ·
                      refine ⟨2052072033705651315970915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43777536719053894740712853 2052072033705651315970915)
                      ·
                        rfl

theorem cell23_3996396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_3996396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996396 prefixEnd_3996396 := by exact prefixLift 3996396
  have htrace : WordTrace (prefixWord ++ tailWord_3996396) baseStart_3996396 baseEnd_3996396 := by
    simpa [prefixWord, tailWord_3996396, baseEnd_3996396] using wordTrace_append hprefix tailTrace_3996396
  have hstable : (prefixWord ++ tailWord_3996396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996396).length < 2 ^ (prefixWord ++ tailWord_3996396).sum := by decide
  have hdescent : baseEnd_3996396 < baseStart_3996396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996400 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2]
def baseStart_3996400 : Nat := 118140960795 + 3996400 * 2 ^ 59
def prefixEnd_3996400 : Nat := 4983230072969 + 3 ^ 40 * 3996400 * 2
def baseEnd_3996400 : Nat := 2052074087628269300320897

theorem tailTrace_3996400 : CollatzResearch.WordTrace tailWord_3996400 prefixEnd_3996400 2052074087628269300320897 := by
  unfold tailWord_3996400
  simp only [CollatzResearch.WordTrace]
  refine ⟨72880341360866402813029327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97173788481155203750705769 72880341360866402813029327)
  ·
    refine ⟨109320512041299604219543991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72880341360866402813029327 109320512041299604219543991)
    ·
      refine ⟨163980768061949406329315987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109320512041299604219543991 163980768061949406329315987)
      ·
        refine ⟨245971152092924109493973981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163980768061949406329315987 245971152092924109493973981)
        ·
          refine ⟨92239182034846541060240243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 245971152092924109493973981 92239182034846541060240243)
          ·
            refine ⟨138358773052269811590360365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92239182034846541060240243 138358773052269811590360365)
            ·
              refine ⟨51884539894601179346385137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138358773052269811590360365 51884539894601179346385137)
              ·
                refine ⟨38913404920950884509788853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51884539894601179346385137 38913404920950884509788853)
                ·
                  refine ⟨3648131711339145422792705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38913404920950884509788853 3648131711339145422792705)
                  ·
                    refine ⟨2736098783504359067094529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648131711339145422792705 2736098783504359067094529)
                    ·
                      refine ⟨2052074087628269300320897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736098783504359067094529 2052074087628269300320897)
                      ·
                        rfl

theorem cell23_3996400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2].length) (baseStart_3996400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996400 prefixEnd_3996400 := by exact prefixLift 3996400
  have htrace : WordTrace (prefixWord ++ tailWord_3996400) baseStart_3996400 baseEnd_3996400 := by
    simpa [prefixWord, tailWord_3996400, baseEnd_3996400] using wordTrace_append hprefix tailTrace_3996400
  have hstable : (prefixWord ++ tailWord_3996400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996400).length < 2 ^ (prefixWord ++ tailWord_3996400).sum := by decide
  have hdescent : baseEnd_3996400 < baseStart_3996400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996410 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_3996410 : Nat := 118140960795 + 3996410 * 2 ^ 59
def prefixEnd_3996410 : Nat := 4983230072969 + 3 ^ 40 * 3996410 * 2
def baseEnd_3996410 : Nat := 684026407478271420398617

theorem tailTrace_3996410 : CollatzResearch.WordTrace tailWord_3996410 prefixEnd_3996410 684026407478271420398617 := by
  unfold tailWord_3996410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36440261862924144333480671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97174031634464384889281789 36440261862924144333480671)
  ·
    refine ⟨54660392794386216500221007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36440261862924144333480671 54660392794386216500221007)
    ·
      refine ⟨81990589191579324750331511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54660392794386216500221007 81990589191579324750331511)
      ·
        refine ⟨122985883787368987125497267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81990589191579324750331511 122985883787368987125497267)
        ·
          refine ⟨184478825681053480688245901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122985883787368987125497267 184478825681053480688245901)
          ·
            refine ⟨69179559630395055258092213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184478825681053480688245901 69179559630395055258092213)
            ·
              refine ⟨6485583715349536430446145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69179559630395055258092213 6485583715349536430446145)
              ·
                refine ⟨4864187786512152322834609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485583715349536430446145 4864187786512152322834609)
                ·
                  refine ⟨3648140839884114242125957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864187786512152322834609 3648140839884114242125957)
                  ·
                    refine ⟨684026407478271420398617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648140839884114242125957 684026407478271420398617)
                    ·
                      rfl

theorem cell23_3996410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_3996410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996410 prefixEnd_3996410 := by exact prefixLift 3996410
  have htrace : WordTrace (prefixWord ++ tailWord_3996410) baseStart_3996410 baseEnd_3996410 := by
    simpa [prefixWord, tailWord_3996410, baseEnd_3996410] using wordTrace_append hprefix tailTrace_3996410
  have hstable : (prefixWord ++ tailWord_3996410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996410).length < 2 ^ (prefixWord ++ tailWord_3996410).sum := by decide
  have hdescent : baseEnd_3996410 < baseStart_3996410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996434 : List Nat := [3, 2, 4, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3996434 : Nat := 118140960795 + 3996434 * 2 ^ 59
def prefixEnd_3996434 : Nat := 4983230072969 + 3 ^ 40 * 3996434 * 2
def baseEnd_3996434 : Nat := 2052091545970522167295741

theorem tailTrace_3996434 : CollatzResearch.WordTrace tailWord_3996434 prefixEnd_3996434 2052091545970522167295741 := by
  unfold tailWord_3996434
  simp only [CollatzResearch.WordTrace]
  refine ⟨36440480700902407358199089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97174615202406419621864237 36440480700902407358199089)
  ·
    refine ⟨27330360525676805518649317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36440480700902407358199089 27330360525676805518649317)
    ·
      refine ⟨5124442598564401034746747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27330360525676805518649317 5124442598564401034746747)
      ·
        refine ⟨7686663897846601552120121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124442598564401034746747 7686663897846601552120121)
        ·
          refine ⟨5764997923384951164090091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7686663897846601552120121 5764997923384951164090091)
          ·
            refine ⟨8647496885077426746135137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764997923384951164090091 8647496885077426746135137)
            ·
              refine ⟨6485622663808070059601353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8647496885077426746135137 6485622663808070059601353)
              ·
                refine ⟨4864216997856052544701015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485622663808070059601353 4864216997856052544701015)
                ·
                  refine ⟨7296325496784078817051523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864216997856052544701015 7296325496784078817051523)
                  ·
                    refine ⟨10944488245176118225577285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296325496784078817051523 10944488245176118225577285)
                    ·
                      refine ⟨2052091545970522167295741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10944488245176118225577285 2052091545970522167295741)
                      ·
                        rfl

theorem cell23_3996434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3996434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996434 prefixEnd_3996434 := by exact prefixLift 3996434
  have htrace : WordTrace (prefixWord ++ tailWord_3996434) baseStart_3996434 baseEnd_3996434 := by
    simpa [prefixWord, tailWord_3996434, baseEnd_3996434] using wordTrace_append hprefix tailTrace_3996434
  have hstable : (prefixWord ++ tailWord_3996434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996434).length < 2 ^ (prefixWord ++ tailWord_3996434).sum := by decide
  have hdescent : baseEnd_3996434 < baseStart_3996434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996468 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_3996468 : Nat := 118140960795 + 3996468 * 2 ^ 59
def prefixEnd_3996468 : Nat := 4983230072969 + 3 ^ 40 * 3996468 * 2
def baseEnd_3996468 : Nat := 2052109004312775034270585

theorem tailTrace_3996468 : CollatzResearch.WordTrace tailWord_3996468 prefixEnd_3996468 2052109004312775034270585 := by
  unfold tailWord_3996468
  simp only [CollatzResearch.WordTrace]
  refine ⟨72881581442743226619767029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97175441923657635493022705 72881581442743226619767029)
  ·
    refine ⟨6832648260257177495603159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72881581442743226619767029 6832648260257177495603159)
    ·
      refine ⟨10248972390385766243404739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6832648260257177495603159 10248972390385766243404739)
      ·
        refine ⟨15373458585578649365107109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10248972390385766243404739 15373458585578649365107109)
        ·
          refine ⟨2882523484795996755957583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15373458585578649365107109 2882523484795996755957583)
          ·
            refine ⟨4323785227193995133936375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882523484795996755957583 4323785227193995133936375)
            ·
              refine ⟨6485677840790992700904563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4323785227193995133936375 6485677840790992700904563)
              ·
                refine ⟨9728516761186489051356845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6485677840790992700904563 9728516761186489051356845)
                ·
                  refine ⟨3648193785444933394258817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9728516761186489051356845 3648193785444933394258817)
                  ·
                    refine ⟨2736145339083700045694113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648193785444933394258817 2736145339083700045694113)
                    ·
                      refine ⟨2052109004312775034270585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736145339083700045694113 2052109004312775034270585)
                      ·
                        rfl

theorem cell23_3996468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_3996468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996468 prefixEnd_3996468 := by exact prefixLift 3996468
  have htrace : WordTrace (prefixWord ++ tailWord_3996468) baseStart_3996468 baseEnd_3996468 := by
    simpa [prefixWord, tailWord_3996468, baseEnd_3996468] using wordTrace_append hprefix tailTrace_3996468
  have hstable : (prefixWord ++ tailWord_3996468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996468).length < 2 ^ (prefixWord ++ tailWord_3996468).sum := by decide
  have hdescent : baseEnd_3996468 < baseStart_3996468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996524 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_3996524 : Nat := 118140960795 + 3996524 * 2 ^ 59
def prefixEnd_3996524 : Nat := 4983230072969 + 3 ^ 40 * 3996524 * 2
def baseEnd_3996524 : Nat := 2052137759229426815170327

theorem tailTrace_3996524 : CollatzResearch.WordTrace tailWord_3996524 prefixEnd_3996524 2052137759229426815170327 := by
  unfold tailWord_3996524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72882602686641787401786313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97176803582189049869048417 72882602686641787401786313)
  ·
    refine ⟨54661952014981340551339735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72882602686641787401786313 54661952014981340551339735)
    ·
      refine ⟨81992928022472010827009603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54661952014981340551339735 81992928022472010827009603)
      ·
        refine ⟨122989392033708016240514405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81992928022472010827009603 122989392033708016240514405)
        ·
          refine ⟨23060511006320253045096451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122989392033708016240514405 23060511006320253045096451)
          ·
            refine ⟨34590766509480379567644677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23060511006320253045096451 34590766509480379567644677)
            ·
              refine ⟨6485768720527571168933377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34590766509480379567644677 6485768720527571168933377)
              ·
                refine ⟨4864326540395678376700033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6485768720527571168933377 4864326540395678376700033)
                ·
                  refine ⟨3648244905296758782525025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864326540395678376700033 3648244905296758782525025)
                  ·
                    refine ⟨2736183678972569086893769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648244905296758782525025 2736183678972569086893769)
                    ·
                      refine ⟨2052137759229426815170327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736183678972569086893769 2052137759229426815170327)
                      ·
                        rfl

theorem cell23_3996524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_3996524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996524 prefixEnd_3996524 := by exact prefixLift 3996524
  have htrace : WordTrace (prefixWord ++ tailWord_3996524) baseStart_3996524 baseEnd_3996524 := by
    simpa [prefixWord, tailWord_3996524, baseEnd_3996524] using wordTrace_append hprefix tailTrace_3996524
  have hstable : (prefixWord ++ tailWord_3996524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996524).length < 2 ^ (prefixWord ++ tailWord_3996524).sum := by decide
  have hdescent : baseEnd_3996524 < baseStart_3996524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996543 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 4, 5]
def baseStart_3996543 : Nat := 118140960795 + 3996543 * 2 ^ 59
def prefixEnd_3996543 : Nat := 4983230072969 + 3 ^ 40 * 3996543 * 2
def baseEnd_3996543 : Nat := 684049171787287413610913

theorem tailTrace_3996543 : CollatzResearch.WordTrace tailWord_3996543 prefixEnd_3996543 684049171787287413610913 := by
  unfold tailWord_3996543
  simp only [CollatzResearch.WordTrace]
  refine ⟨145765898360214741048514283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97177265573476494032342855 145765898360214741048514283)
  ·
    refine ⟨218648847540322111572771425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145765898360214741048514283 218648847540322111572771425)
    ·
      refine ⟨163986635655241583679578569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218648847540322111572771425 163986635655241583679578569)
      ·
        refine ⟨122989976741431187759683927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163986635655241583679578569 122989976741431187759683927)
        ·
          refine ⟨184484965112146781639525891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122989976741431187759683927 184484965112146781639525891)
          ·
            refine ⟨276727447668220172459288837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184484965112146781639525891 276727447668220172459288837)
            ·
              refine ⟨51886396437791282336116657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 276727447668220172459288837 51886396437791282336116657)
              ·
                refine ⟨38914797328343461752087493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51886396437791282336116657 38914797328343461752087493)
                ·
                  refine ⟨7296524499064399078516405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38914797328343461752087493 7296524499064399078516405)
                  ·
                    refine ⟨684049171787287413610913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296524499064399078516405 684049171787287413610913)
                    ·
                      rfl

theorem cell23_3996543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_3996543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996543 prefixEnd_3996543 := by exact prefixLift 3996543
  have htrace : WordTrace (prefixWord ++ tailWord_3996543) baseStart_3996543 baseEnd_3996543 := by
    simpa [prefixWord, tailWord_3996543, baseEnd_3996543] using wordTrace_append hprefix tailTrace_3996543
  have hstable : (prefixWord ++ tailWord_3996543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996543).length < 2 ^ (prefixWord ++ tailWord_3996543).sum := by decide
  have hdescent : baseEnd_3996543 < baseStart_3996543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996580 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3996580 : Nat := 118140960795 + 3996580 * 2 ^ 59
def prefixEnd_3996580 : Nat := 4983230072969 + 3 ^ 40 * 3996580 * 2
def baseEnd_3996580 : Nat := 2052166514146078596070069

theorem tailTrace_3996580 : CollatzResearch.WordTrace tailWord_3996580 prefixEnd_3996580 2052166514146078596070069 := by
  unfold tailWord_3996580
  simp only [CollatzResearch.WordTrace]
  refine ⟨72883623930540348183805597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97178165240720464245074129 72883623930540348183805597)
  ·
    refine ⟨27331358973952630568927099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72883623930540348183805597 27331358973952630568927099)
    ·
      refine ⟨40997038460928945853390649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27331358973952630568927099 40997038460928945853390649)
      ·
        refine ⟨30747778845696709390042987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40997038460928945853390649 30747778845696709390042987)
        ·
          refine ⟨46121668268545064085064481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30747778845696709390042987 46121668268545064085064481)
          ·
            refine ⟨34591251201408798063798361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46121668268545064085064481 34591251201408798063798361)
            ·
              refine ⟨25943438401056598547848771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34591251201408798063798361 25943438401056598547848771)
              ·
                refine ⟨38915157601584897821773157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25943438401056598547848771 38915157601584897821773157)
                ·
                  refine ⟨7296592050297168341582467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38915157601584897821773157 7296592050297168341582467)
                  ·
                    refine ⟨10944888075445752512373701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7296592050297168341582467 10944888075445752512373701)
                    ·
                      refine ⟨2052166514146078596070069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10944888075445752512373701 2052166514146078596070069)
                      ·
                        rfl

theorem cell23_3996580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3996580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996580 prefixEnd_3996580 := by exact prefixLift 3996580
  have htrace : WordTrace (prefixWord ++ tailWord_3996580) baseStart_3996580 baseEnd_3996580 := by
    simpa [prefixWord, tailWord_3996580, baseEnd_3996580] using wordTrace_append hprefix tailTrace_3996580
  have hstable : (prefixWord ++ tailWord_3996580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996580).length < 2 ^ (prefixWord ++ tailWord_3996580).sum := by decide
  have hdescent : baseEnd_3996580 < baseStart_3996580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996597 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3996597 : Nat := 118140960795 + 3996597 * 2 ^ 59
def prefixEnd_3996597 : Nat := 4983230072969 + 3 ^ 40 * 3996597 * 2
def baseEnd_3996597 : Nat := 2052175243317205029557491

theorem tailTrace_3996597 : CollatzResearch.WordTrace tailWord_3996597 prefixEnd_3996597 2052175243317205029557491 := by
  unfold tailWord_3996597
  simp only [CollatzResearch.WordTrace]
  refine ⟨145767867902019108270980045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97178578601346072180653363 145767867902019108270980045)
  ·
    refine ⟨54662950463257165601617517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145767867902019108270980045 54662950463257165601617517)
    ·
      refine ⟨20498606423721437100606569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54662950463257165601617517 20498606423721437100606569)
      ·
        refine ⟨15373954817791077825454927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20498606423721437100606569 15373954817791077825454927)
        ·
          refine ⟨23060932226686616738182391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15373954817791077825454927 23060932226686616738182391)
          ·
            refine ⟨34591398340029925107273587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23060932226686616738182391 34591398340029925107273587)
            ·
              refine ⟨51887097510044887660910381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34591398340029925107273587 51887097510044887660910381)
              ·
                refine ⟨19457661566266832872841393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51887097510044887660910381 19457661566266832872841393)
                ·
                  refine ⟨14593246174700124654631045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19457661566266832872841393 14593246174700124654631045)
                  ·
                    refine ⟨2736233657756273372743321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14593246174700124654631045 2736233657756273372743321)
                    ·
                      refine ⟨2052175243317205029557491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736233657756273372743321 2052175243317205029557491)
                      ·
                        rfl

theorem cell23_3996597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3996597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996597 prefixEnd_3996597 := by exact prefixLift 3996597
  have htrace : WordTrace (prefixWord ++ tailWord_3996597) baseStart_3996597 baseEnd_3996597 := by
    simpa [prefixWord, tailWord_3996597, baseEnd_3996597] using wordTrace_append hprefix tailTrace_3996597
  have hstable : (prefixWord ++ tailWord_3996597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996597).length < 2 ^ (prefixWord ++ tailWord_3996597).sum := by decide
  have hdescent : baseEnd_3996597 < baseStart_3996597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996600 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_3996600 : Nat := 118140960795 + 3996600 * 2 ^ 59
def prefixEnd_3996600 : Nat := 4983230072969 + 3 ^ 40 * 3996600 * 2
def baseEnd_3996600 : Nat := 2052176783759168517819977

theorem tailTrace_3996600 : CollatzResearch.WordTrace tailWord_3996600 prefixEnd_3996600 2052176783759168517819977 := by
  unfold tailWord_3996600
  simp only [CollatzResearch.WordTrace]
  refine ⟨72883988660504119891669627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97178651547338826522226169 72883988660504119891669627)
  ·
    refine ⟨109325982990756179837504441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72883988660504119891669627 109325982990756179837504441)
    ·
      refine ⟨81994487243067134878128331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109325982990756179837504441 81994487243067134878128331)
      ·
        refine ⟨122991730864600702317192497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81994487243067134878128331 122991730864600702317192497)
        ·
          refine ⟨92243798148450526737894373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122991730864600702317192497 92243798148450526737894373)
          ·
            refine ⟨17295712152834473763355195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92243798148450526737894373 17295712152834473763355195)
            ·
              refine ⟨25943568229251710645032793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17295712152834473763355195 25943568229251710645032793)
              ·
                refine ⟨19457676171938782983774595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25943568229251710645032793 19457676171938782983774595)
                ·
                  refine ⟨29186514257908174475661893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19457676171938782983774595 29186514257908174475661893)
                  ·
                    refine ⟨5472471423357782714186605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29186514257908174475661893 5472471423357782714186605)
                    ·
                      refine ⟨2052176783759168517819977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5472471423357782714186605 2052176783759168517819977)
                      ·
                        rfl

theorem cell23_3996600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_3996600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996600 prefixEnd_3996600 := by exact prefixLift 3996600
  have htrace : WordTrace (prefixWord ++ tailWord_3996600) baseStart_3996600 baseEnd_3996600 := by
    simpa [prefixWord, tailWord_3996600, baseEnd_3996600] using wordTrace_append hprefix tailTrace_3996600
  have hstable : (prefixWord ++ tailWord_3996600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996600).length < 2 ^ (prefixWord ++ tailWord_3996600).sum := by decide
  have hdescent : baseEnd_3996600 < baseStart_3996600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996680 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_3996680 : Nat := 118140960795 + 3996680 * 2 ^ 59
def prefixEnd_3996680 : Nat := 4983230072969 + 3 ^ 40 * 3996680 * 2
def baseEnd_3996680 : Nat := 684072620737176068273203

theorem tailTrace_3996680 : CollatzResearch.WordTrace tailWord_3996680 prefixEnd_3996680 684072620737176068273203 := by
  unfold tailWord_3996680
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885447580359206723125747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97180596773812275630834329 72885447580359206723125747)
  ·
    refine ⟨109328171370538810084688621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72885447580359206723125747 109328171370538810084688621)
    ·
      refine ⟨40998064263952053781758233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109328171370538810084688621 40998064263952053781758233)
      ·
        refine ⟨30748548197964040336318675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40998064263952053781758233 30748548197964040336318675)
        ·
          refine ⟨46122822296946060504478013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30748548197964040336318675 46122822296946060504478013)
          ·
            refine ⟨17296058361354772689179255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46122822296946060504478013 17296058361354772689179255)
            ·
              refine ⟨25944087542032159033768883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296058361354772689179255 25944087542032159033768883)
              ·
                refine ⟨38916131313048238550653325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25944087542032159033768883 38916131313048238550653325)
                ·
                  refine ⟨14593549242393089456494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38916131313048238550653325 14593549242393089456494997)
                  ·
                    refine ⟨684072620737176068273203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14593549242393089456494997 684072620737176068273203)
                    ·
                      rfl

theorem cell23_3996680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_3996680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996680 prefixEnd_3996680 := by exact prefixLift 3996680
  have htrace : WordTrace (prefixWord ++ tailWord_3996680) baseStart_3996680 baseEnd_3996680 := by
    simpa [prefixWord, tailWord_3996680, baseEnd_3996680] using wordTrace_append hprefix tailTrace_3996680
  have hstable : (prefixWord ++ tailWord_3996680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996680).length < 2 ^ (prefixWord ++ tailWord_3996680).sum := by decide
  have hdescent : baseEnd_3996680 < baseStart_3996680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996684 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_3996684 : Nat := 118140960795 + 3996684 * 2 ^ 59
def prefixEnd_3996684 : Nat := 4983230072969 + 3 ^ 40 * 3996684 * 2
def baseEnd_3996684 : Nat := 684073305378048729723197

theorem tailTrace_3996684 : CollatzResearch.WordTrace tailWord_3996684 prefixEnd_3996684 684073305378048729723197 := by
  unfold tailWord_3996684
  simp only [CollatzResearch.WordTrace]
  refine ⟨72885520526351961064698553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97180694035135948086264737 72885520526351961064698553)
  ·
    refine ⟨54664140394763970798523915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72885520526351961064698553 54664140394763970798523915)
    ·
      refine ⟨81996210592145956197785873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54664140394763970798523915 81996210592145956197785873)
      ·
        refine ⟨61497157944109467148339405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81996210592145956197785873 61497157944109467148339405)
        ·
          refine ⟨23061434229041050180627277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61497157944109467148339405 23061434229041050180627277)
          ·
            refine ⟨8648037835890393817735229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23061434229041050180627277 8648037835890393817735229)
            ·
              refine ⟨3243014188458897681650711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8648037835890393817735229 3243014188458897681650711)
              ·
                refine ⟨4864521282688346522476067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243014188458897681650711 4864521282688346522476067)
                ·
                  refine ⟨7296781924032519783714101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864521282688346522476067 7296781924032519783714101)
                  ·
                    refine ⟨684073305378048729723197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7296781924032519783714101 684073305378048729723197)
                    ·
                      rfl

theorem cell23_3996684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_3996684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996684 prefixEnd_3996684 := by exact prefixLift 3996684
  have htrace : WordTrace (prefixWord ++ tailWord_3996684) baseStart_3996684 baseEnd_3996684 := by
    simpa [prefixWord, tailWord_3996684, baseEnd_3996684] using wordTrace_append hprefix tailTrace_3996684
  have hstable : (prefixWord ++ tailWord_3996684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996684).length < 2 ^ (prefixWord ++ tailWord_3996684).sum := by decide
  have hdescent : baseEnd_3996684 < baseStart_3996684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996697 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_3996697 : Nat := 118140960795 + 3996697 * 2 ^ 59
def prefixEnd_3996697 : Nat := 4983230072969 + 3 ^ 40 * 3996697 * 2
def baseEnd_3996697 : Nat := 684075530460884879435677

theorem tailTrace_3996697 : CollatzResearch.WordTrace tailWord_3996697 prefixEnd_3996697 684075530460884879435677 := by
  unfold tailWord_3996697
  simp only [CollatzResearch.WordTrace]
  refine ⟨145771515201656825349620345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97181010134437883566413563 145771515201656825349620345)
  ·
    refine ⟨109328636401242619012215259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145771515201656825349620345 109328636401242619012215259)
    ·
      refine ⟨163992954601863928518322889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109328636401242619012215259 163992954601863928518322889)
      ·
        refine ⟨122994715951397946388742167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163992954601863928518322889 122994715951397946388742167)
        ·
          refine ⟨184492073927096919583113251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122994715951397946388742167 184492073927096919583113251)
          ·
            refine ⟨276738110890645379374669877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184492073927096919583113251 276738110890645379374669877)
            ·
              refine ⟨25944197895998004316375301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 276738110890645379374669877 25944197895998004316375301)
              ·
                refine ⟨4864537105499625809320369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25944197895998004316375301 4864537105499625809320369)
                ·
                  refine ⟨3648402829124719356990277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864537105499625809320369 3648402829124719356990277)
                  ·
                    refine ⟨684075530460884879435677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648402829124719356990277 684075530460884879435677)
                    ·
                      rfl

theorem cell23_3996697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_3996697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996697 prefixEnd_3996697 := by exact prefixLift 3996697
  have htrace : WordTrace (prefixWord ++ tailWord_3996697) baseStart_3996697 baseEnd_3996697 := by
    simpa [prefixWord, tailWord_3996697, baseEnd_3996697] using wordTrace_append hprefix tailTrace_3996697
  have hstable : (prefixWord ++ tailWord_3996697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996697).length < 2 ^ (prefixWord ++ tailWord_3996697).sum := by decide
  have hdescent : baseEnd_3996697 < baseStart_3996697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996707 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3]
def baseStart_3996707 : Nat := 118140960795 + 3996707 * 2 ^ 59
def prefixEnd_3996707 : Nat := 4983230072969 + 3 ^ 40 * 3996707 * 2
def baseEnd_3996707 : Nat := 2052231726189199599181985

theorem tailTrace_3996707 : CollatzResearch.WordTrace tailWord_3996707 prefixEnd_3996707 2052231726189199599181985 := by
  unfold tailWord_3996707
  simp only [CollatzResearch.WordTrace]
  refine ⟨145771879931620597057484375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97181253287747064704989583 145771879931620597057484375)
  ·
    refine ⟨218657819897430895586226563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145771879931620597057484375 218657819897430895586226563)
    ·
      refine ⟨327986729846146343379339845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218657819897430895586226563 327986729846146343379339845)
      ·
        refine ⟨61497511846152439383626221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 327986729846146343379339845 61497511846152439383626221)
        ·
          refine ⟨23061566942307164768859833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61497511846152439383626221 23061566942307164768859833)
          ·
            refine ⟨17296175206730373576644875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23061566942307164768859833 17296175206730373576644875)
            ·
              refine ⟨25944262810095560364967313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296175206730373576644875 25944262810095560364967313)
              ·
                refine ⟨19458197107571670273725485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25944262810095560364967313 19458197107571670273725485)
                ·
                  refine ⟨7296823915339376352647057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19458197107571670273725485 7296823915339376352647057)
                  ·
                    refine ⟨5472617936504532264485293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7296823915339376352647057 5472617936504532264485293)
                    ·
                      refine ⟨2052231726189199599181985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5472617936504532264485293 2052231726189199599181985)
                      ·
                        rfl

theorem cell23_3996707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_3996707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996707 prefixEnd_3996707 := by exact prefixLift 3996707
  have htrace : WordTrace (prefixWord ++ tailWord_3996707) baseStart_3996707 baseEnd_3996707 := by
    simpa [prefixWord, tailWord_3996707, baseEnd_3996707] using wordTrace_append hprefix tailTrace_3996707
  have hstable : (prefixWord ++ tailWord_3996707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996707).length < 2 ^ (prefixWord ++ tailWord_3996707).sum := by decide
  have hdescent : baseEnd_3996707 < baseStart_3996707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996714 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3996714 : Nat := 118140960795 + 3996714 * 2 ^ 59
def prefixEnd_3996714 : Nat := 4983230072969 + 3 ^ 40 * 3996714 * 2
def baseEnd_3996714 : Nat := 684078440184593690598151

theorem tailTrace_3996714 : CollatzResearch.WordTrace tailWord_3996714 prefixEnd_3996714 684078440184593690598151 := by
  unfold tailWord_3996714
  simp only [CollatzResearch.WordTrace]
  refine ⟨36443033810648809313247299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97181423495063491501992797 36443033810648809313247299)
  ·
    refine ⟨54664550715973213969870949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36443033810648809313247299 54664550715973213969870949)
    ·
      refine ⟨10249603259244977619350803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54664550715973213969870949 10249603259244977619350803)
      ·
        refine ⟨15374404888867466429026205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10249603259244977619350803 15374404888867466429026205)
        ·
          refine ⟨5765401833325299910884827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15374404888867466429026205 5765401833325299910884827)
          ·
            refine ⟨8648102749987949866327241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765401833325299910884827 8648102749987949866327241)
            ·
              refine ⟨6486077062490962399745431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8648102749987949866327241 6486077062490962399745431)
              ·
                refine ⟨9729115593736443599618147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486077062490962399745431 9729115593736443599618147)
                ·
                  refine ⟨14593673390604665399427221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729115593736443599618147 14593673390604665399427221)
                  ·
                    refine ⟨684078440184593690598151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14593673390604665399427221 684078440184593690598151)
                    ·
                      rfl

theorem cell23_3996714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3996714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996714 prefixEnd_3996714 := by exact prefixLift 3996714
  have htrace : WordTrace (prefixWord ++ tailWord_3996714) baseStart_3996714 baseEnd_3996714 := by
    simpa [prefixWord, tailWord_3996714, baseEnd_3996714] using wordTrace_append hprefix tailTrace_3996714
  have hstable : (prefixWord ++ tailWord_3996714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996714).length < 2 ^ (prefixWord ++ tailWord_3996714).sum := by decide
  have hdescent : baseEnd_3996714 < baseStart_3996714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996734 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3996734 : Nat := 118140960795 + 3996734 * 2 ^ 59
def prefixEnd_3996734 : Nat := 4983230072969 + 3 ^ 40 * 3996734 * 2
def baseEnd_3996734 : Nat := 2052245590166870993544361

theorem tailTrace_3996734 : CollatzResearch.WordTrace tailWord_3996734 prefixEnd_3996734 2052245590166870993544361 := by
  unfold tailWord_3996734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18221608087815347583589657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97181909801681853779144837 18221608087815347583589657)
  ·
    refine ⟨13666206065861510687692243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18221608087815347583589657 13666206065861510687692243)
    ·
      refine ⟨20499309098792266031538365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13666206065861510687692243 20499309098792266031538365)
      ·
        refine ⟨7687240912047099761826887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20499309098792266031538365 7687240912047099761826887)
        ·
          refine ⟨11530861368070649642740331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7687240912047099761826887 11530861368070649642740331)
          ·
            refine ⟨17296292052105974464110497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11530861368070649642740331 17296292052105974464110497)
            ·
              refine ⟨12972219039079480848082873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17296292052105974464110497 12972219039079480848082873)
              ·
                refine ⟨9729164279309610636062155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12972219039079480848082873 9729164279309610636062155)
                ·
                  refine ⟨14593746418964415954093233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9729164279309610636062155 14593746418964415954093233)
                  ·
                    refine ⟨10945309814223311965569925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14593746418964415954093233 10945309814223311965569925)
                    ·
                      refine ⟨2052245590166870993544361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10945309814223311965569925 2052245590166870993544361)
                      ·
                        rfl

theorem cell23_3996734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3996734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996734 prefixEnd_3996734 := by exact prefixLift 3996734
  have htrace : WordTrace (prefixWord ++ tailWord_3996734) baseStart_3996734 baseEnd_3996734 := by
    simpa [prefixWord, tailWord_3996734, baseEnd_3996734] using wordTrace_append hprefix tailTrace_3996734
  have hstable : (prefixWord ++ tailWord_3996734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996734).length < 2 ^ (prefixWord ++ tailWord_3996734).sum := by decide
  have hdescent : baseEnd_3996734 < baseStart_3996734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996781 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_3996781 : Nat := 118140960795 + 3996781 * 2 ^ 59
def prefixEnd_3996781 : Nat := 4983230072969 + 3 ^ 40 * 3996781 * 2
def baseEnd_3996781 : Nat := 2052269723757632309656645

theorem tailTrace_3996781 : CollatzResearch.WordTrace tailWord_3996781 prefixEnd_3996781 2052269723757632309656645 := by
  unfold tailWord_3996781
  simp only [CollatzResearch.WordTrace]
  refine ⟨145774578933352507695678197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97183052622235005130452131 145774578933352507695678197)
  ·
    refine ⟨13666366775001797596469831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 145774578933352507695678197 13666366775001797596469831)
    ·
      refine ⟨20499550162502696394704747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13666366775001797596469831 20499550162502696394704747)
      ·
        refine ⟨30749325243754044592057121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20499550162502696394704747 30749325243754044592057121)
        ·
          refine ⟨23061993932815533444042841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30749325243754044592057121 23061993932815533444042841)
          ·
            refine ⟨17296495449611650083032131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23061993932815533444042841 17296495449611650083032131)
            ·
              refine ⟨25944743174417475124548197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296495449611650083032131 25944743174417475124548197)
              ·
                refine ⟨4864639345203276585852787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25944743174417475124548197 4864639345203276585852787)
                ·
                  refine ⟨7296959017804914878779181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864639345203276585852787 7296959017804914878779181)
                  ·
                    refine ⟨2736359631676843079542193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7296959017804914878779181 2736359631676843079542193)
                    ·
                      refine ⟨2052269723757632309656645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736359631676843079542193 2052269723757632309656645)
                      ·
                        rfl

theorem cell23_3996781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_3996781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996781 prefixEnd_3996781 := by exact prefixLift 3996781
  have htrace : WordTrace (prefixWord ++ tailWord_3996781) baseStart_3996781 baseEnd_3996781 := by
    simpa [prefixWord, tailWord_3996781, baseEnd_3996781] using wordTrace_append hprefix tailTrace_3996781
  have hstable : (prefixWord ++ tailWord_3996781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996781).length < 2 ^ (prefixWord ++ tailWord_3996781).sum := by decide
  have hdescent : baseEnd_3996781 < baseStart_3996781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996789 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3996789 : Nat := 118140960795 + 3996789 * 2 ^ 59
def prefixEnd_3996789 : Nat := 4983230072969 + 3 ^ 40 * 3996789 * 2
def baseEnd_3996789 : Nat := 2052273831602868278356609

theorem tailTrace_3996789 : CollatzResearch.WordTrace tailWord_3996789 prefixEnd_3996789 2052273831602868278356609 := by
  unfold tailWord_3996789
  simp only [CollatzResearch.WordTrace]
  refine ⟨145774870717323525061969421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97183247144882350041312947 145774870717323525061969421)
  ·
    refine ⟨54665576518996321898238533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145774870717323525061969421 54665576518996321898238533)
    ·
      refine ⟨10249795597311810355919725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54665576518996321898238533 10249795597311810355919725)
      ·
        refine ⟨3843673348991928883469897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10249795597311810355919725 3843673348991928883469897)
        ·
          refine ⟨2882755011743946662602423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3843673348991928883469897 2882755011743946662602423)
          ·
            refine ⟨4324132517615919993903635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882755011743946662602423 4324132517615919993903635)
            ·
              refine ⟨6486198776423879990855453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324132517615919993903635 6486198776423879990855453)
              ·
                refine ⟨2432324541158954996570795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6486198776423879990855453 2432324541158954996570795)
                ·
                  refine ⟨3648486811738432494856193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432324541158954996570795 3648486811738432494856193)
                  ·
                    refine ⟨2736365108803824371142145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648486811738432494856193 2736365108803824371142145)
                    ·
                      refine ⟨2052273831602868278356609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736365108803824371142145 2052273831602868278356609)
                      ·
                        rfl

theorem cell23_3996789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3996789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996789 prefixEnd_3996789 := by exact prefixLift 3996789
  have htrace : WordTrace (prefixWord ++ tailWord_3996789) baseStart_3996789 baseEnd_3996789 := by
    simpa [prefixWord, tailWord_3996789, baseEnd_3996789] using wordTrace_append hprefix tailTrace_3996789
  have hstable : (prefixWord ++ tailWord_3996789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996789).length < 2 ^ (prefixWord ++ tailWord_3996789).sum := by decide
  have hdescent : baseEnd_3996789 < baseStart_3996789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996797 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3996797 : Nat := 118140960795 + 3996797 * 2 ^ 59
def prefixEnd_3996797 : Nat := 4983230072969 + 3 ^ 40 * 3996797 * 2
def baseEnd_3996797 : Nat := 2052277939448104247056571

theorem tailTrace_3996797 : CollatzResearch.WordTrace tailWord_3996797 prefixEnd_3996797 2052277939448104247056571 := by
  unfold tailWord_3996797
  simp only [CollatzResearch.WordTrace]
  refine ⟨145775162501294542428260645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97183441667529694952173763 145775162501294542428260645)
  ·
    refine ⟨27332842968992726705298871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145775162501294542428260645 27332842968992726705298871)
    ·
      refine ⟨40999264453489090057948307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27332842968992726705298871 40999264453489090057948307)
      ·
        refine ⟨61498896680233635086922461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40999264453489090057948307 61498896680233635086922461)
        ·
          refine ⟨23062086255087613157595923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61498896680233635086922461 23062086255087613157595923)
          ·
            refine ⟨34593129382631419736393885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23062086255087613157595923 34593129382631419736393885)
            ·
              refine ⟨12972423518486782401147707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34593129382631419736393885 12972423518486782401147707)
              ·
                refine ⟨19458635277730173601721561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972423518486782401147707 19458635277730173601721561)
                ·
                  refine ⟨14593976458297630201291171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19458635277730173601721561 14593976458297630201291171)
                  ·
                    refine ⟨21890964687446445301936757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14593976458297630201291171 21890964687446445301936757)
                    ·
                      refine ⟨2052277939448104247056571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21890964687446445301936757 2052277939448104247056571)
                      ·
                        rfl

theorem cell23_3996797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3996797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996797 prefixEnd_3996797 := by exact prefixLift 3996797
  have htrace : WordTrace (prefixWord ++ tailWord_3996797) baseStart_3996797 baseEnd_3996797 := by
    simpa [prefixWord, tailWord_3996797, baseEnd_3996797] using wordTrace_append hprefix tailTrace_3996797
  have hstable : (prefixWord ++ tailWord_3996797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996797).length < 2 ^ (prefixWord ++ tailWord_3996797).sum := by decide
  have hdescent : baseEnd_3996797 < baseStart_3996797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996800 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 9]
def baseStart_3996800 : Nat := 118140960795 + 3996800 * 2 ^ 59
def prefixEnd_3996800 : Nat := 4983230072969 + 3 ^ 40 * 3996800 * 2
def baseEnd_3996800 : Nat := 228031053321118637257673

theorem tailTrace_3996800 : CollatzResearch.WordTrace tailWord_3996800 prefixEnd_3996800 228031053321118637257673 := by
  unfold tailWord_3996800
  simp only [CollatzResearch.WordTrace]
  refine ⟨72887635960141836970309927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97183514613522449293746569 72887635960141836970309927)
  ·
    refine ⟨109331453940212755455464891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72887635960141836970309927 109331453940212755455464891)
    ·
      refine ⟨163997180910319133183197337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109331453940212755455464891 163997180910319133183197337)
      ·
        refine ⟨122997885682739349887398003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163997180910319133183197337 122997885682739349887398003)
        ·
          refine ⟨184496828524109024831097005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122997885682739349887398003 184496828524109024831097005)
          ·
            refine ⟨69186310696540884311661377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184496828524109024831097005 69186310696540884311661377)
            ·
              refine ⟨51889733022405663233746033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69186310696540884311661377 51889733022405663233746033)
              ·
                refine ⟨38917299766804247425309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51889733022405663233746033 38917299766804247425309525)
                ·
                  refine ⟨228031053321118637257673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38917299766804247425309525 228031053321118637257673)
                  ·
                    rfl

theorem cell23_3996800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_3996800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996800 prefixEnd_3996800 := by exact prefixLift 3996800
  have htrace : WordTrace (prefixWord ++ tailWord_3996800) baseStart_3996800 baseEnd_3996800 := by
    simpa [prefixWord, tailWord_3996800, baseEnd_3996800] using wordTrace_append hprefix tailTrace_3996800
  have hstable : (prefixWord ++ tailWord_3996800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996800).length < 2 ^ (prefixWord ++ tailWord_3996800).sum := by decide
  have hdescent : baseEnd_3996800 < baseStart_3996800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996828 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3996828 : Nat := 118140960795 + 3996828 * 2 ^ 59
def prefixEnd_3996828 : Nat := 4983230072969 + 3 ^ 40 * 3996828 * 2
def baseEnd_3996828 : Nat := 2052293857348393625768929

theorem tailTrace_3996828 : CollatzResearch.WordTrace tailWord_3996828 prefixEnd_3996828 2052293857348393625768929 := by
  unfold tailWord_3996828
  simp only [CollatzResearch.WordTrace]
  refine ⟨72888146582091117361319569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97184195442788156481759425 72888146582091117361319569)
  ·
    refine ⟨54666109936568338020989677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72888146582091117361319569 54666109936568338020989677)
    ·
      refine ⟨20499791226213126757871129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54666109936568338020989677 20499791226213126757871129)
      ·
        refine ⟨15374843419659845068403347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20499791226213126757871129 15374843419659845068403347)
        ·
          refine ⟨23062265129489767602605021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15374843419659845068403347 23062265129489767602605021)
          ·
            refine ⟨8648349423558662850976883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23062265129489767602605021 8648349423558662850976883)
            ·
              refine ⟨12972524135337994276465325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648349423558662850976883 12972524135337994276465325)
              ·
                refine ⟨4864696550751747853674497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12972524135337994276465325 4864696550751747853674497)
                ·
                  refine ⟨3648522413063810890255873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4864696550751747853674497 3648522413063810890255873)
                  ·
                    refine ⟨2736391809797858167691905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3648522413063810890255873 2736391809797858167691905)
                    ·
                      refine ⟨2052293857348393625768929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736391809797858167691905 2052293857348393625768929)
                      ·
                        rfl

theorem cell23_3996828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3996828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996828 prefixEnd_3996828 := by exact prefixLift 3996828
  have htrace : WordTrace (prefixWord ++ tailWord_3996828) baseStart_3996828 baseEnd_3996828 := by
    simpa [prefixWord, tailWord_3996828, baseEnd_3996828] using wordTrace_append hprefix tailTrace_3996828
  have hstable : (prefixWord ++ tailWord_3996828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996828).length < 2 ^ (prefixWord ++ tailWord_3996828).sum := by decide
  have hdescent : baseEnd_3996828 < baseStart_3996828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996847 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 2, 5]
def baseStart_3996847 : Nat := 118140960795 + 3996847 * 2 ^ 59
def prefixEnd_3996847 : Nat := 4983230072969 + 3 ^ 40 * 3996847 * 2
def baseEnd_3996847 : Nat := 684101204493609683810447

theorem tailTrace_3996847 : CollatzResearch.WordTrace tailWord_3996847 prefixEnd_3996847 684101204493609683810447 := by
  unfold tailWord_3996847
  simp only [CollatzResearch.WordTrace]
  refine ⟨145776986151113400967580795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97184657434075600645053863 145776986151113400967580795)
  ·
    refine ⟨218665479226670101451371193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145776986151113400967580795 218665479226670101451371193)
    ·
      refine ⟨163999109420002576088528395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218665479226670101451371193 163999109420002576088528395)
      ·
        refine ⟨245998664130003864132792593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163999109420002576088528395 245998664130003864132792593)
        ·
          refine ⟨184498998097502898099594445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245998664130003864132792593 184498998097502898099594445)
          ·
            refine ⟨69187124286563586787347917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184498998097502898099594445 69187124286563586787347917)
            ·
              refine ⟨25945171607461345045255469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69187124286563586787347917 25945171607461345045255469)
              ·
                refine ⟨9729439352798004391970801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25945171607461345045255469 9729439352798004391970801)
                ·
                  refine ⟨7297079514598503293978101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729439352798004391970801 7297079514598503293978101)
                  ·
                    refine ⟨684101204493609683810447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7297079514598503293978101 684101204493609683810447)
                    ·
                      rfl

theorem cell23_3996847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_3996847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996847 prefixEnd_3996847 := by exact prefixLift 3996847
  have htrace : WordTrace (prefixWord ++ tailWord_3996847) baseStart_3996847 baseEnd_3996847 := by
    simpa [prefixWord, tailWord_3996847, baseEnd_3996847] using wordTrace_append hprefix tailTrace_3996847
  have hstable : (prefixWord ++ tailWord_3996847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996847).length < 2 ^ (prefixWord ++ tailWord_3996847).sum := by decide
  have hdescent : baseEnd_3996847 < baseStart_3996847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996857 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3996857 : Nat := 118140960795 + 3996857 * 2 ^ 59
def prefixEnd_3996857 : Nat := 4983230072969 + 3 ^ 40 * 3996857 * 2
def baseEnd_3996857 : Nat := 2052308748287374012306295

theorem tailTrace_3996857 : CollatzResearch.WordTrace tailWord_3996857 prefixEnd_3996857 2052308748287374012306295 := by
  unfold tailWord_3996857
  simp only [CollatzResearch.WordTrace]
  refine ⟨145777350881077172675444825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97184900587384781783629883 145777350881077172675444825)
  ·
    refine ⟨109333013160807879506583619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145777350881077172675444825 109333013160807879506583619)
    ·
      refine ⟨163999519741211819259875429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109333013160807879506583619 163999519741211819259875429)
      ·
        refine ⟨30749909951477216111226643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163999519741211819259875429 30749909951477216111226643)
        ·
          refine ⟨46124864927215824166839965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30749909951477216111226643 46124864927215824166839965)
          ·
            refine ⟨17296824347705934062564987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46124864927215824166839965 17296824347705934062564987)
            ·
              refine ⟨25945236521558901093847481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17296824347705934062564987 25945236521558901093847481)
              ·
                refine ⟨19458927391169175820385611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25945236521558901093847481 19458927391169175820385611)
                ·
                  refine ⟨29188391086753763730578417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19458927391169175820385611 29188391086753763730578417)
                  ·
                    refine ⟨21891293315065322797933813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29188391086753763730578417 21891293315065322797933813)
                    ·
                      refine ⟨2052308748287374012306295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21891293315065322797933813 2052308748287374012306295)
                      ·
                        rfl

theorem cell23_3996857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3996857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996857 prefixEnd_3996857 := by exact prefixLift 3996857
  have htrace : WordTrace (prefixWord ++ tailWord_3996857) baseStart_3996857 baseEnd_3996857 := by
    simpa [prefixWord, tailWord_3996857, baseEnd_3996857] using wordTrace_append hprefix tailTrace_3996857
  have hstable : (prefixWord ++ tailWord_3996857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996857).length < 2 ^ (prefixWord ++ tailWord_3996857).sum := by decide
  have hdescent : baseEnd_3996857 < baseStart_3996857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996867 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4]
def baseStart_3996867 : Nat := 118140960795 + 3996867 * 2 ^ 59
def prefixEnd_3996867 : Nat := 4983230072969 + 3 ^ 40 * 3996867 * 2
def baseEnd_3996867 : Nat := 2052313883093918973181249

theorem tailTrace_3996867 : CollatzResearch.WordTrace tailWord_3996867 prefixEnd_3996867 2052313883093918973181249 := by
  unfold tailWord_3996867
  simp only [CollatzResearch.WordTrace]
  refine ⟨145777715611040944383308855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97185143740693962922205903 145777715611040944383308855)
  ·
    refine ⟨218666573416561416574963283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145777715611040944383308855 218666573416561416574963283)
    ·
      refine ⟨327999860124842124862444925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218666573416561416574963283 327999860124842124862444925)
      ·
        refine ⟨122999947546815796823416847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327999860124842124862444925 122999947546815796823416847)
        ·
          refine ⟨184499921320223695235125271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122999947546815796823416847 184499921320223695235125271)
          ·
            refine ⟨276749881980335542852687907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184499921320223695235125271 276749881980335542852687907)
            ·
              refine ⟨415124822970503314279031861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276749881980335542852687907 415124822970503314279031861)
              ·
                refine ⟨38917952153484685713659237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 415124822970503314279031861 38917952153484685713659237)
                ·
                  refine ⟨7297116028778378571311107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38917952153484685713659237 7297116028778378571311107)
                  ·
                    refine ⟨10945674043167567856966661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297116028778378571311107 10945674043167567856966661)
                    ·
                      refine ⟨2052313883093918973181249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10945674043167567856966661 2052313883093918973181249)
                      ·
                        rfl

theorem cell23_3996867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_3996867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996867 prefixEnd_3996867 := by exact prefixLift 3996867
  have htrace : WordTrace (prefixWord ++ tailWord_3996867) baseStart_3996867 baseEnd_3996867 := by
    simpa [prefixWord, tailWord_3996867, baseEnd_3996867] using wordTrace_append hprefix tailTrace_3996867
  have hstable : (prefixWord ++ tailWord_3996867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996867).length < 2 ^ (prefixWord ++ tailWord_3996867).sum := by decide
  have hdescent : baseEnd_3996867 < baseStart_3996867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996904 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3996904 : Nat := 118140960795 + 3996904 * 2 ^ 59
def prefixEnd_3996904 : Nat := 4983230072969 + 3 ^ 40 * 3996904 * 2
def baseEnd_3996904 : Nat := 2052332881878135328418579

theorem tailTrace_3996904 : CollatzResearch.WordTrace tailWord_3996904 prefixEnd_3996904 2052332881878135328418579 := by
  unfold tailWord_3996904
  simp only [CollatzResearch.WordTrace]
  refine ⟨72889532555953449851202883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97186043407937933134937177 72889532555953449851202883)
  ·
    refine ⟨109334298833930174776804325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72889532555953449851202883 109334298833930174776804325)
    ·
      refine ⟨20500181031361907770650811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109334298833930174776804325 20500181031361907770650811)
      ·
        refine ⟨30750271547042861655976217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500181031361907770650811 30750271547042861655976217)
        ·
          refine ⟨23062703660282146241982163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30750271547042861655976217 23062703660282146241982163)
          ·
            refine ⟨34594055490423219362973245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23062703660282146241982163 34594055490423219362973245)
            ·
              refine ⟨12972770808908707261114967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34594055490423219362973245 12972770808908707261114967)
              ·
                refine ⟨19459156213363060891672451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972770808908707261114967 19459156213363060891672451)
                ·
                  refine ⟨29188734320044591337508677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19459156213363060891672451 29188734320044591337508677)
                  ·
                    refine ⟨5472887685008360875782877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29188734320044591337508677 5472887685008360875782877)
                    ·
                      refine ⟨2052332881878135328418579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5472887685008360875782877 2052332881878135328418579)
                      ·
                        rfl

theorem cell23_3996904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3996904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996904 prefixEnd_3996904 := by exact prefixLift 3996904
  have htrace : WordTrace (prefixWord ++ tailWord_3996904) baseStart_3996904 baseEnd_3996904 := by
    simpa [prefixWord, tailWord_3996904, baseEnd_3996904] using wordTrace_append hprefix tailTrace_3996904
  have hstable : (prefixWord ++ tailWord_3996904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996904).length < 2 ^ (prefixWord ++ tailWord_3996904).sum := by decide
  have hdescent : baseEnd_3996904 < baseStart_3996904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996924 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 8]
def baseStart_3996924 : Nat := 118140960795 + 3996924 * 2 ^ 59
def prefixEnd_3996924 : Nat := 4983230072969 + 3 ^ 40 * 3996924 * 2
def baseEnd_3996924 : Nat := 228038127943469472240943

theorem tailTrace_3996924 : CollatzResearch.WordTrace tailWord_3996924 prefixEnd_3996924 228038127943469472240943 := by
  unfold tailWord_3996924
  simp only [CollatzResearch.WordTrace]
  refine ⟨72889897285917221559066913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97186529714556295412089217 72889897285917221559066913)
  ·
    refine ⟨54667422964437916169300185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72889897285917221559066913 54667422964437916169300185)
    ·
      refine ⟨41000567223328437126975139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54667422964437916169300185 41000567223328437126975139)
      ·
        refine ⟨61500850834992655690462709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41000567223328437126975139 61500850834992655690462709)
        ·
          refine ⟨5765704765780561470980879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61500850834992655690462709 5765704765780561470980879)
          ·
            refine ⟨8648557148670842206471319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5765704765780561470980879 8648557148670842206471319)
            ·
              refine ⟨12972835723006263309706979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648557148670842206471319 12972835723006263309706979)
              ·
                refine ⟨19459253584509394964560469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12972835723006263309706979 19459253584509394964560469)
                ·
                  refine ⟨228038127943469472240943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19459253584509394964560469 228038127943469472240943)
                  ·
                    rfl

theorem cell23_3996924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_3996924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996924 prefixEnd_3996924 := by exact prefixLift 3996924
  have htrace : WordTrace (prefixWord ++ tailWord_3996924) baseStart_3996924 baseEnd_3996924 := by
    simpa [prefixWord, tailWord_3996924, baseEnd_3996924] using wordTrace_append hprefix tailTrace_3996924
  have hstable : (prefixWord ++ tailWord_3996924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996924).length < 2 ^ (prefixWord ++ tailWord_3996924).sum := by decide
  have hdescent : baseEnd_3996924 < baseStart_3996924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996927 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_3996927 : Nat := 118140960795 + 3996927 * 2 ^ 59
def prefixEnd_3996927 : Nat := 4983230072969 + 3 ^ 40 * 3996927 * 2
def baseEnd_3996927 : Nat := 2052344691933188738430973

theorem tailTrace_3996927 : CollatzResearch.WordTrace tailWord_3996927 prefixEnd_3996927 2052344691933188738430973 := by
  unfold tailWord_3996927
  simp only [CollatzResearch.WordTrace]
  refine ⟨145779903990823574630493035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97186602660549049753662023 145779903990823574630493035)
  ·
    refine ⟨218669855986235361945739553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145779903990823574630493035 218669855986235361945739553)
    ·
      refine ⟨164002391989676521459304665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218669855986235361945739553 164002391989676521459304665)
      ·
        refine ⟨123001793992257391094478499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164002391989676521459304665 123001793992257391094478499)
        ·
          refine ⟨184502690988386086641717749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123001793992257391094478499 184502690988386086641717749)
          ·
            refine ⟨17297127280161195622661039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184502690988386086641717749 17297127280161195622661039)
            ·
              refine ⟨25945690920241793433991559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17297127280161195622661039 25945690920241793433991559)
              ·
                refine ⟨38918536380362690150987339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25945690920241793433991559 38918536380362690150987339)
                ·
                  refine ⟨58377804570544035226481009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38918536380362690150987339 58377804570544035226481009)
                  ·
                    refine ⟨43783353427908026419860757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58377804570544035226481009 43783353427908026419860757)
                    ·
                      refine ⟨2052344691933188738430973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43783353427908026419860757 2052344691933188738430973)
                      ·
                        rfl

theorem cell23_3996927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_3996927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996927 prefixEnd_3996927 := by exact prefixLift 3996927
  have htrace : WordTrace (prefixWord ++ tailWord_3996927) baseStart_3996927 baseEnd_3996927 := by
    simpa [prefixWord, tailWord_3996927, baseEnd_3996927] using wordTrace_append hprefix tailTrace_3996927
  have hstable : (prefixWord ++ tailWord_3996927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996927).length < 2 ^ (prefixWord ++ tailWord_3996927).sum := by decide
  have hdescent : baseEnd_3996927 < baseStart_3996927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996951 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3996951 : Nat := 118140960795 + 3996951 * 2 ^ 59
def prefixEnd_3996951 : Nat := 4983230072969 + 3 ^ 40 * 3996951 * 2
def baseEnd_3996951 : Nat := 2052357015468896644530863

theorem tailTrace_3996951 : CollatzResearch.WordTrace tailWord_3996951 prefixEnd_3996951 2052357015468896644530863 := by
  unfold tailWord_3996951
  simp only [CollatzResearch.WordTrace]
  refine ⟨145780779342736626729366707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97187186228491084486244471 145780779342736626729366707)
  ·
    refine ⟨218671169014104940094050061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145780779342736626729366707 218671169014104940094050061)
    ·
      refine ⟨82001688380289352535268773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 218671169014104940094050061 82001688380289352535268773)
      ·
        refine ⟨15375316571304253600362895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82001688380289352535268773 15375316571304253600362895)
        ·
          refine ⟨23062974856956380400544343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15375316571304253600362895 23062974856956380400544343)
          ·
            refine ⟨34594462285434570600816515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23062974856956380400544343 34594462285434570600816515)
            ·
              refine ⟨51891693428151855901224773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34594462285434570600816515 51891693428151855901224773)
              ·
                refine ⟨9729692517778472981479645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51891693428151855901224773 9729692517778472981479645)
                ·
                  refine ⟨3648634694166927368054867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9729692517778472981479645 3648634694166927368054867)
                  ·
                    refine ⟨5472952041250391052082301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3648634694166927368054867 5472952041250391052082301)
                    ·
                      refine ⟨2052357015468896644530863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5472952041250391052082301 2052357015468896644530863)
                      ·
                        rfl

theorem cell23_3996951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3996951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996951 prefixEnd_3996951 := by exact prefixLift 3996951
  have htrace : WordTrace (prefixWord ++ tailWord_3996951) baseStart_3996951 baseEnd_3996951 := by
    simpa [prefixWord, tailWord_3996951, baseEnd_3996951] using wordTrace_append hprefix tailTrace_3996951
  have hstable : (prefixWord ++ tailWord_3996951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996951).length < 2 ^ (prefixWord ++ tailWord_3996951).sum := by decide
  have hdescent : baseEnd_3996951 < baseStart_3996951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996961 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3996961 : Nat := 118140960795 + 3996961 * 2 ^ 59
def prefixEnd_3996961 : Nat := 4983230072969 + 3 ^ 40 * 3996961 * 2
def baseEnd_3996961 : Nat := 2052362150275441605405817

theorem tailTrace_3996961 : CollatzResearch.WordTrace tailWord_3996961 prefixEnd_3996961 2052362150275441605405817 := by
  unfold tailWord_3996961
  simp only [CollatzResearch.WordTrace]
  refine ⟨145781144072700398437230737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97187429381800265624820491 145781144072700398437230737)
  ·
    refine ⟨109335858054525298827923053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145781144072700398437230737 109335858054525298827923053)
    ·
      refine ⟨41000946770446987060471145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109335858054525298827923053 41000946770446987060471145)
      ·
        refine ⟨30750710077835240295353359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41000946770446987060471145 30750710077835240295353359)
        ·
          refine ⟨46126065116752860443030039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30750710077835240295353359 46126065116752860443030039)
          ·
            refine ⟨69189097675129290664545059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46126065116752860443030039 69189097675129290664545059)
            ·
              refine ⟨103783646512693935996817589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69189097675129290664545059 103783646512693935996817589)
              ·
                refine ⟨9729716860565056499701649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103783646512693935996817589 9729716860565056499701649)
                ·
                  refine ⟨7297287645423792374776237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729716860565056499701649 7297287645423792374776237)
                  ·
                    refine ⟨2736482867033922140541089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7297287645423792374776237 2736482867033922140541089)
                    ·
                      refine ⟨2052362150275441605405817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736482867033922140541089 2052362150275441605405817)
                      ·
                        rfl

theorem cell23_3996961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3996961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996961 prefixEnd_3996961 := by exact prefixLift 3996961
  have htrace : WordTrace (prefixWord ++ tailWord_3996961) baseStart_3996961 baseEnd_3996961 := by
    simpa [prefixWord, tailWord_3996961, baseEnd_3996961] using wordTrace_append hprefix tailTrace_3996961
  have hstable : (prefixWord ++ tailWord_3996961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996961).length < 2 ^ (prefixWord ++ tailWord_3996961).sum := by decide
  have hdescent : baseEnd_3996961 < baseStart_3996961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996962 : List Nat := [3, 3, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3996962 : Nat := 118140960795 + 3996962 * 2 ^ 59
def prefixEnd_3996962 : Nat := 4983230072969 + 3 ^ 40 * 3996962 * 2
def baseEnd_3996962 : Nat := 684120887918698700497771

theorem tailTrace_3996962 : CollatzResearch.WordTrace tailWord_3996962 prefixEnd_3996962 684120887918698700497771 := by
  unfold tailWord_3996962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445295136424193902004285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97187453697131183738678093 36445295136424193902004285)
  ·
    refine ⟨13666985676159072713251607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36445295136424193902004285 13666985676159072713251607)
    ·
      refine ⟨20500478514238609069877411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13666985676159072713251607 20500478514238609069877411)
      ·
        refine ⟨30750717771357913604816117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20500478514238609069877411 30750717771357913604816117)
        ·
          refine ⟨2882879791064804400451511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30750717771357913604816117 2882879791064804400451511)
          ·
            refine ⟨4324319686597206600677267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882879791064804400451511 4324319686597206600677267)
            ·
              refine ⟨6486479529895809901015901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324319686597206600677267 6486479529895809901015901)
              ·
                refine ⟨2432429823710928712880963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6486479529895809901015901 2432429823710928712880963)
                ·
                  refine ⟨3648644735566393069321445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2432429823710928712880963 3648644735566393069321445)
                  ·
                    refine ⟨684120887918698700497771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3648644735566393069321445 684120887918698700497771)
                    ·
                      rfl

theorem cell23_3996962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3996962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996962 prefixEnd_3996962 := by exact prefixLift 3996962
  have htrace : WordTrace (prefixWord ++ tailWord_3996962) baseStart_3996962 baseEnd_3996962 := by
    simpa [prefixWord, tailWord_3996962, baseEnd_3996962] using wordTrace_append hprefix tailTrace_3996962
  have hstable : (prefixWord ++ tailWord_3996962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996962).length < 2 ^ (prefixWord ++ tailWord_3996962).sum := by decide
  have hdescent : baseEnd_3996962 < baseStart_3996962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996978 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2]
def baseStart_3996978 : Nat := 118140960795 + 3996978 * 2 ^ 59
def prefixEnd_3996978 : Nat := 4983230072969 + 3 ^ 40 * 3996978 * 2
def baseEnd_3996978 : Nat := 2052370879446568038893239

theorem tailTrace_3996978 : CollatzResearch.WordTrace tailWord_3996978 prefixEnd_3996978 2052370879446568038893239 := by
  unfold tailWord_3996978
  simp only [CollatzResearch.WordTrace]
  refine ⟨36445441028409702585149897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97187842742425873560399725 36445441028409702585149897)
  ·
    refine ⟨27334080771307276938862423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36445441028409702585149897 27334080771307276938862423)
    ·
      refine ⟨41001121156960915408293635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27334080771307276938862423 41001121156960915408293635)
      ·
        refine ⟨61501681735441373112440453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41001121156960915408293635 61501681735441373112440453)
        ·
          refine ⟨11531565325395257458582585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61501681735441373112440453 11531565325395257458582585)
          ·
            refine ⟨8648673994046443093936939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11531565325395257458582585 8648673994046443093936939)
            ·
              refine ⟨12973010991069664640905409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648673994046443093936939 12973010991069664640905409)
              ·
                refine ⟨9729758243302248480679057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12973010991069664640905409 9729758243302248480679057)
                ·
                  refine ⟨7297318682476686360509293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9729758243302248480679057 7297318682476686360509293)
                  ·
                    refine ⟨2736494505928757385190985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7297318682476686360509293 2736494505928757385190985)
                    ·
                      refine ⟨2052370879446568038893239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736494505928757385190985 2052370879446568038893239)
                      ·
                        rfl

theorem cell23_3996978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_3996978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996978 prefixEnd_3996978 := by exact prefixLift 3996978
  have htrace : WordTrace (prefixWord ++ tailWord_3996978) baseStart_3996978 baseEnd_3996978 := by
    simpa [prefixWord, tailWord_3996978, baseEnd_3996978] using wordTrace_append hprefix tailTrace_3996978
  have hstable : (prefixWord ++ tailWord_3996978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996978).length < 2 ^ (prefixWord ++ tailWord_3996978).sum := by decide
  have hdescent : baseEnd_3996978 < baseStart_3996978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3996985 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3996985 : Nat := 118140960795 + 3996985 * 2 ^ 59
def prefixEnd_3996985 : Nat := 4983230072969 + 3 ^ 40 * 3996985 * 2
def baseEnd_3996985 : Nat := 2052374473811149511505707

theorem tailTrace_3996985 : CollatzResearch.WordTrace tailWord_3996985 prefixEnd_3996985 2052374473811149511505707 := by
  unfold tailWord_3996985
  simp only [CollatzResearch.WordTrace]
  refine ⟨145782019424613450536104409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97188012949742300357402939 145782019424613450536104409)
  ·
    refine ⟨109336514568460087902078307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145782019424613450536104409 109336514568460087902078307)
    ·
      refine ⟨164004771852690131853117461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109336514568460087902078307 164004771852690131853117461)
      ·
        refine ⟨7687723680594849930614881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164004771852690131853117461 7687723680594849930614881)
        ·
          refine ⟨5765792760446137447961161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7687723680594849930614881 5765792760446137447961161)
          ·
            refine ⟨4324344570334603085970871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5765792760446137447961161 4324344570334603085970871)
            ·
              refine ⟨6486516855501904628956307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324344570334603085970871 6486516855501904628956307)
              ·
                refine ⟨9729775283252856943434461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6486516855501904628956307 9729775283252856943434461)
                ·
                  refine ⟨3648665731219821353787923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9729775283252856943434461 3648665731219821353787923)
                  ·
                    refine ⟨5472998596829732030681885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3648665731219821353787923 5472998596829732030681885)
                    ·
                      refine ⟨2052374473811149511505707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5472998596829732030681885 2052374473811149511505707)
                      ·
                        rfl

theorem cell23_3996985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3996985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3996985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3996985 prefixEnd_3996985 := by exact prefixLift 3996985
  have htrace : WordTrace (prefixWord ++ tailWord_3996985) baseStart_3996985 baseEnd_3996985 := by
    simpa [prefixWord, tailWord_3996985, baseEnd_3996985] using wordTrace_append hprefix tailTrace_3996985
  have hstable : (prefixWord ++ tailWord_3996985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3996985).length < 2 ^ (prefixWord ++ tailWord_3996985).sum := by decide
  have hdescent : baseEnd_3996985 < baseStart_3996985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3996985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997004 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3997004 : Nat := 118140960795 + 3997004 * 2 ^ 59
def prefixEnd_3997004 : Nat := 4983230072969 + 3 ^ 40 * 3997004 * 2
def baseEnd_3997004 : Nat := 2052384229943584937168119

theorem tailTrace_3997004 : CollatzResearch.WordTrace tailWord_3997004 prefixEnd_3997004 2052384229943584937168119 := by
  unfold tailWord_3997004
  simp only [CollatzResearch.WordTrace]
  refine ⟨72891356205772308390523033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97188474941029744520697377 72891356205772308390523033)
  ·
    refine ⟨54668517154329231292892275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72891356205772308390523033 54668517154329231292892275)
    ·
      refine ⟨82002775731493846939338413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54668517154329231292892275 82002775731493846939338413)
      ·
        refine ⟨30751040899310192602251905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82002775731493846939338413 30751040899310192602251905)
        ·
          refine ⟨23063280674482644451688929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30751040899310192602251905 23063280674482644451688929)
          ·
            refine ⟨17297460505861983338766697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23063280674482644451688929 17297460505861983338766697)
            ·
              refine ⟨12973095379396487504075023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17297460505861983338766697 12973095379396487504075023)
              ·
                refine ⟨19459643069094731256112535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12973095379396487504075023 19459643069094731256112535)
                ·
                  refine ⟨29189464603642096884168803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19459643069094731256112535 29189464603642096884168803)
                  ·
                    refine ⟨43784196905463145326253205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29189464603642096884168803 43784196905463145326253205)
                    ·
                      refine ⟨2052384229943584937168119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43784196905463145326253205 2052384229943584937168119)
                      ·
                        rfl

theorem cell23_3997004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3997004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997004 prefixEnd_3997004 := by exact prefixLift 3997004
  have htrace : WordTrace (prefixWord ++ tailWord_3997004) baseStart_3997004 baseEnd_3997004 := by
    simpa [prefixWord, tailWord_3997004, baseEnd_3997004] using wordTrace_append hprefix tailTrace_3997004
  have hstable : (prefixWord ++ tailWord_3997004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997004).length < 2 ^ (prefixWord ++ tailWord_3997004).sum := by decide
  have hdescent : baseEnd_3997004 < baseStart_3997004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997041 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_3997041 : Nat := 118140960795 + 3997041 * 2 ^ 59
def prefixEnd_3997041 : Nat := 4983230072969 + 3 ^ 40 * 3997041 * 2
def baseEnd_3997041 : Nat := 2052403228727801292405449

theorem tailTrace_3997041 : CollatzResearch.WordTrace tailWord_3997041 prefixEnd_3997041 2052403228727801292405449 := by
  unfold tailWord_3997041
  simp only [CollatzResearch.WordTrace]
  refine ⟨145784061912410572100142977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97189374608273714733428651 145784061912410572100142977)
  ·
    refine ⟨109338046434307929075107233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145784061912410572100142977 109338046434307929075107233)
    ·
      refine ⟨82003534825730946806330425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109338046434307929075107233 82003534825730946806330425)
      ·
        refine ⟨61502651119298210104747819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82003534825730946806330425 61502651119298210104747819)
        ·
          refine ⟨92253976678947315157121729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61502651119298210104747819 92253976678947315157121729)
          ·
            refine ⟨69190482509210486367841297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92253976678947315157121729 69190482509210486367841297)
            ·
              refine ⟨51892861881907864775880973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69190482509210486367841297 51892861881907864775880973)
              ·
                refine ⟨19459823205715449290955365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51892861881907864775880973 19459823205715449290955365)
                ·
                  refine ⟨3648716851071646742054131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19459823205715449290955365 3648716851071646742054131)
                  ·
                    refine ⟨5473075276607470113081197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3648716851071646742054131 5473075276607470113081197)
                    ·
                      refine ⟨2052403228727801292405449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5473075276607470113081197 2052403228727801292405449)
                      ·
                        rfl

theorem cell23_3997041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_3997041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997041 prefixEnd_3997041 := by exact prefixLift 3997041
  have htrace : WordTrace (prefixWord ++ tailWord_3997041) baseStart_3997041 baseEnd_3997041 := by
    simpa [prefixWord, tailWord_3997041, baseEnd_3997041] using wordTrace_append hprefix tailTrace_3997041
  have hstable : (prefixWord ++ tailWord_3997041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997041).length < 2 ^ (prefixWord ++ tailWord_3997041).sum := by decide
  have hdescent : baseEnd_3997041 < baseStart_3997041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997051 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 5, 3, 2]
def baseStart_3997051 : Nat := 118140960795 + 3997051 * 2 ^ 59
def prefixEnd_3997051 : Nat := 4983230072969 + 3 ^ 40 * 3997051 * 2
def baseEnd_3997051 : Nat := 2052408363534346253280403

theorem tailTrace_3997051 : CollatzResearch.WordTrace tailWord_3997051 prefixEnd_3997051 2052408363534346253280403 := by
  unfold tailWord_3997051
  simp only [CollatzResearch.WordTrace]
  refine ⟨145784426642374343808007007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97189617761582895872004671 145784426642374343808007007)
  ·
    refine ⟨218676639963561515712010511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145784426642374343808007007 218676639963561515712010511)
    ·
      refine ⟨328014959945342273568015767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218676639963561515712010511 328014959945342273568015767)
      ·
        refine ⟨492022439918013410352023651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328014959945342273568015767 492022439918013410352023651)
        ·
          refine ⟨738033659877020115528035477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492022439918013410352023651 738033659877020115528035477)
          ·
            refine ⟨34595327806735317915376663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 738033659877020115528035477 34595327806735317915376663)
            ·
              refine ⟨51892991710102976873064995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34595327806735317915376663 51892991710102976873064995)
              ·
                refine ⟨77839487565154465309597493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51892991710102976873064995 77839487565154465309597493)
                ·
                  refine ⟨7297451959233231122774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77839487565154465309597493 7297451959233231122774765)
                  ·
                    refine ⟨2736544484712461671040537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7297451959233231122774765 2736544484712461671040537)
                    ·
                      refine ⟨2052408363534346253280403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736544484712461671040537 2052408363534346253280403)
                      ·
                        rfl

theorem cell23_3997051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 3, 2].length) (baseStart_3997051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997051 prefixEnd_3997051 := by exact prefixLift 3997051
  have htrace : WordTrace (prefixWord ++ tailWord_3997051) baseStart_3997051 baseEnd_3997051 := by
    simpa [prefixWord, tailWord_3997051, baseEnd_3997051] using wordTrace_append hprefix tailTrace_3997051
  have hstable : (prefixWord ++ tailWord_3997051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997051).length < 2 ^ (prefixWord ++ tailWord_3997051).sum := by decide
  have hdescent : baseEnd_3997051 < baseStart_3997051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997068 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_3997068 : Nat := 118140960795 + 3997068 * 2 ^ 59
def prefixEnd_3997068 : Nat := 4983230072969 + 3 ^ 40 * 3997068 * 2
def baseEnd_3997068 : Nat := 2052417092705472686767825

theorem tailTrace_3997068 : CollatzResearch.WordTrace tailWord_3997068 prefixEnd_3997068 2052417092705472686767825 := by
  unfold tailWord_3997068
  simp only [CollatzResearch.WordTrace]
  refine ⟨72892523341656377855687929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97190031122208503807583905 72892523341656377855687929)
  ·
    refine ⟨54669392506242283391765947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72892523341656377855687929 54669392506242283391765947)
    ·
      refine ⟨82004088759363425087648921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54669392506242283391765947 82004088759363425087648921)
      ·
        refine ⟨61503066569522568815736691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82004088759363425087648921 61503066569522568815736691)
        ·
          refine ⟨92254599854283853223605037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61503066569522568815736691 92254599854283853223605037)
          ·
            refine ⟨34595474945356444958851889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92254599854283853223605037 34595474945356444958851889)
            ·
              refine ⟨25946606209017333719138917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34595474945356444958851889 25946606209017333719138917)
              ·
                refine ⟨4864988664190750072338547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25946606209017333719138917 4864988664190750072338547)
                ·
                  refine ⟨7297482996286125108507821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4864988664190750072338547 7297482996286125108507821)
                  ·
                    refine ⟨2736556123607296915690433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7297482996286125108507821 2736556123607296915690433)
                    ·
                      refine ⟨2052417092705472686767825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736556123607296915690433 2052417092705472686767825)
                      ·
                        rfl

theorem cell23_3997068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_3997068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997068 prefixEnd_3997068 := by exact prefixLift 3997068
  have htrace : WordTrace (prefixWord ++ tailWord_3997068) baseStart_3997068 baseEnd_3997068 := by
    simpa [prefixWord, tailWord_3997068, baseEnd_3997068] using wordTrace_append hprefix tailTrace_3997068
  have hstable : (prefixWord ++ tailWord_3997068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997068).length < 2 ^ (prefixWord ++ tailWord_3997068).sum := by decide
  have hdescent : baseEnd_3997068 < baseStart_3997068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997085 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_3997085 : Nat := 118140960795 + 3997085 * 2 ^ 59
def prefixEnd_3997085 : Nat := 4983230072969 + 3 ^ 40 * 3997085 * 2
def baseEnd_3997085 : Nat := 2052425821876599120255247

theorem tailTrace_3997085 : CollatzResearch.WordTrace tailWord_3997085 prefixEnd_3997085 2052425821876599120255247 := by
  unfold tailWord_3997085
  simp only [CollatzResearch.WordTrace]
  refine ⟨145785666724251167614744709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97190444482834111743163139 145785666724251167614744709)
  ·
    refine ⟨27334812510797093927764633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145785666724251167614744709 27334812510797093927764633)
    ·
      refine ⟨20501109383097820445823475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27334812510797093927764633 20501109383097820445823475)
      ·
        refine ⟨30751664074646730668735213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20501109383097820445823475 30751664074646730668735213)
        ·
          refine ⟨11531874027992524000775705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30751664074646730668735213 11531874027992524000775705)
          ·
            refine ⟨8648905520994393000581779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11531874027992524000775705 8648905520994393000581779)
            ·
              refine ⟨12973358281491589500872669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8648905520994393000581779 12973358281491589500872669)
              ·
                refine ⟨4865009355559346062827251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12973358281491589500872669 4865009355559346062827251)
                ·
                  refine ⟨7297514033339019094240877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865009355559346062827251 7297514033339019094240877)
                  ·
                    refine ⟨2736567762502132160340329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7297514033339019094240877 2736567762502132160340329)
                    ·
                      refine ⟨2052425821876599120255247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736567762502132160340329 2052425821876599120255247)
                      ·
                        rfl

theorem cell23_3997085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_3997085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997085 prefixEnd_3997085 := by exact prefixLift 3997085
  have htrace : WordTrace (prefixWord ++ tailWord_3997085) baseStart_3997085 baseEnd_3997085 := by
    simpa [prefixWord, tailWord_3997085, baseEnd_3997085] using wordTrace_append hprefix tailTrace_3997085
  have hstable : (prefixWord ++ tailWord_3997085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997085).length < 2 ^ (prefixWord ++ tailWord_3997085).sum := by decide
  have hdescent : baseEnd_3997085 < baseStart_3997085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997151 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 2, 5]
def baseStart_3997151 : Nat := 118140960795 + 3997151 * 2 ^ 59
def prefixEnd_3997151 : Nat := 4983230072969 + 3 ^ 40 * 3997151 * 2
def baseEnd_3997151 : Nat := 684153237199931954009981

theorem tailTrace_3997151 : CollatzResearch.WordTrace tailWord_3997151 prefixEnd_3997151 684153237199931954009981 := by
  unfold tailWord_3997151
  simp only [CollatzResearch.WordTrace]
  refine ⟨145788073942012060886647307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97192049294674707257764871 145788073942012060886647307)
  ·
    refine ⟨218682110913018091329970961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145788073942012060886647307 218682110913018091329970961)
    ·
      refine ⟨164011583184763568497478221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218682110913018091329970961 164011583184763568497478221)
      ·
        refine ⟨61504343694286338186554333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164011583184763568497478221 61504343694286338186554333)
        ·
          refine ⟨23064128885357376819957875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61504343694286338186554333 23064128885357376819957875)
          ·
            refine ⟨34596193328036065229936813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23064128885357376819957875 34596193328036065229936813)
            ·
              refine ⟨12973572498013524461226305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34596193328036065229936813 12973572498013524461226305)
              ·
                refine ⟨9730179373510143345919729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12973572498013524461226305 9730179373510143345919729)
                ·
                  refine ⟨7297634530132607509439797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9730179373510143345919729 7297634530132607509439797)
                  ·
                    refine ⟨684153237199931954009981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7297634530132607509439797 684153237199931954009981)
                    ·
                      rfl

theorem cell23_3997151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_3997151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997151 prefixEnd_3997151 := by exact prefixLift 3997151
  have htrace : WordTrace (prefixWord ++ tailWord_3997151) baseStart_3997151 baseEnd_3997151 := by
    simpa [prefixWord, tailWord_3997151, baseEnd_3997151] using wordTrace_append hprefix tailTrace_3997151
  have hstable : (prefixWord ++ tailWord_3997151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997151).length < 2 ^ (prefixWord ++ tailWord_3997151).sum := by decide
  have hdescent : baseEnd_3997151 < baseStart_3997151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997155 : List Nat := [1, 1, 1, 6, 2, 2, 3, 2, 5]
def baseStart_3997155 : Nat := 118140960795 + 3997155 * 2 ^ 59
def prefixEnd_3997155 : Nat := 4983230072969 + 3 ^ 40 * 3997155 * 2
def baseEnd_3997155 : Nat := 228051307280268205153325

theorem tailTrace_3997155 : CollatzResearch.WordTrace tailWord_3997155 prefixEnd_3997155 228051307280268205153325 := by
  unfold tailWord_3997155
  simp only [CollatzResearch.WordTrace]
  refine ⟨145788219833997569569792919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97192146555998379713195279 145788219833997569569792919)
  ·
    refine ⟨218682329750996354354689379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145788219833997569569792919 218682329750996354354689379)
    ·
      refine ⟨328023494626494531532034069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218682329750996354354689379 328023494626494531532034069)
      ·
        refine ⟨15376101310616931165564097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 328023494626494531532034069 15376101310616931165564097)
        ·
          refine ⟨11532075982962698374173073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15376101310616931165564097 11532075982962698374173073)
          ·
            refine ⟨8649056987222023780629805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11532075982962698374173073 8649056987222023780629805)
            ·
              refine ⟨3243396370208258917736177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8649056987222023780629805 3243396370208258917736177)
              ·
                refine ⟨2432547277656194188302133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3243396370208258917736177 2432547277656194188302133)
                ·
                  refine ⟨228051307280268205153325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2432547277656194188302133 228051307280268205153325)
                  ·
                    rfl

theorem cell23_3997155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 5].length) (baseStart_3997155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997155 prefixEnd_3997155 := by exact prefixLift 3997155
  have htrace : WordTrace (prefixWord ++ tailWord_3997155) baseStart_3997155 baseEnd_3997155 := by
    simpa [prefixWord, tailWord_3997155, baseEnd_3997155] using wordTrace_append hprefix tailTrace_3997155
  have hstable : (prefixWord ++ tailWord_3997155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997155).length < 2 ^ (prefixWord ++ tailWord_3997155).sum := by decide
  have hdescent : baseEnd_3997155 < baseStart_3997155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997164 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_3997164 : Nat := 118140960795 + 3997164 * 2 ^ 59
def prefixEnd_3997164 : Nat := 4983230072969 + 3 ^ 40 * 3997164 * 2
def baseEnd_3997164 : Nat := 684155462282768103722461

theorem tailTrace_3997164 : CollatzResearch.WordTrace tailWord_3997164 prefixEnd_3997164 684155462282768103722461 := by
  unfold tailWord_3997164
  simp only [CollatzResearch.WordTrace]
  refine ⟨72894274045482482053435273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97192365393976642737913697 72894274045482482053435273)
  ·
    refine ⟨54670705534111861540076455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72894274045482482053435273 54670705534111861540076455)
    ·
      refine ⟨82006058301167792310114683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54670705534111861540076455 82006058301167792310114683)
      ·
        refine ⟨123009087451751688465172025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82006058301167792310114683 123009087451751688465172025)
        ·
          refine ⟨92256815588813766348879019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123009087451751688465172025 92256815588813766348879019)
          ·
            refine ⟨138385223383220649523318529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92256815588813766348879019 138385223383220649523318529)
            ·
              refine ⟨103788917537415487142488897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138385223383220649523318529 103788917537415487142488897)
              ·
                refine ⟨77841688153061615356866673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103788917537415487142488897 77841688153061615356866673)
                ·
                  refine ⟨58381266114796211517650005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77841688153061615356866673 58381266114796211517650005)
                  ·
                    refine ⟨684155462282768103722461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58381266114796211517650005 684155462282768103722461)
                    ·
                      rfl

theorem cell23_3997164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_3997164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997164 prefixEnd_3997164 := by exact prefixLift 3997164
  have htrace : WordTrace (prefixWord ++ tailWord_3997164) baseStart_3997164 baseEnd_3997164 := by
    simpa [prefixWord, tailWord_3997164, baseEnd_3997164] using wordTrace_append hprefix tailTrace_3997164
  have hstable : (prefixWord ++ tailWord_3997164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997164).length < 2 ^ (prefixWord ++ tailWord_3997164).sum := by decide
  have hdescent : baseEnd_3997164 < baseStart_3997164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997221 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_3997221 : Nat := 118140960795 + 3997221 * 2 ^ 59
def prefixEnd_3997221 : Nat := 4983230072969 + 3 ^ 40 * 3997221 * 2
def baseEnd_3997221 : Nat := 2052495655245610588154621

theorem tailTrace_3997221 : CollatzResearch.WordTrace tailWord_3997221 prefixEnd_3997221 2052495655245610588154621 := by
  unfold tailWord_3997221
  simp only [CollatzResearch.WordTrace]
  refine ⟨145790627051758462841695517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97193751367838975227797011 145790627051758462841695517)
  ·
    refine ⟨54671485144409423565635819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145790627051758462841695517 54671485144409423565635819)
    ·
      refine ⟨82007227716614135348453729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54671485144409423565635819 82007227716614135348453729)
      ·
        refine ⟨61505420787460601511340297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82007227716614135348453729 61505420787460601511340297)
        ·
          refine ⟨46129065590595451133505223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61505420787460601511340297 46129065590595451133505223)
          ·
            refine ⟨69193598385893176700257835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46129065590595451133505223 69193598385893176700257835)
            ·
              refine ⟨103790397578839765050386753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69193598385893176700257835 103790397578839765050386753)
              ·
                refine ⟨77842798184129823787790065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103790397578839765050386753 77842798184129823787790065)
                ·
                  refine ⟨58382098638097367840842549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77842798184129823787790065 58382098638097367840842549)
                  ·
                    refine ⟨5473321747321628235078989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58382098638097367840842549 5473321747321628235078989)
                    ·
                      refine ⟨2052495655245610588154621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5473321747321628235078989 2052495655245610588154621)
                      ·
                        rfl

theorem cell23_3997221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_3997221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997221 prefixEnd_3997221 := by exact prefixLift 3997221
  have htrace : WordTrace (prefixWord ++ tailWord_3997221) baseStart_3997221 baseEnd_3997221 := by
    simpa [prefixWord, tailWord_3997221, baseEnd_3997221] using wordTrace_append hprefix tailTrace_3997221
  have hstable : (prefixWord ++ tailWord_3997221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997221).length < 2 ^ (prefixWord ++ tailWord_3997221).sum := by decide
  have hdescent : baseEnd_3997221 < baseStart_3997221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997258 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_3997258 : Nat := 118140960795 + 3997258 * 2 ^ 59
def prefixEnd_3997258 : Nat := 4983230072969 + 3 ^ 40 * 3997258 * 2
def baseEnd_3997258 : Nat := 684171551343275647797317

theorem tailTrace_3997258 : CollatzResearch.WordTrace tailWord_3997258 prefixEnd_3997258 684171551343275647797317 := by
  unfold tailWord_3997258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36447994138156104540198107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97194651035082945440528285 36447994138156104540198107)
  ·
    refine ⟨54671991207234156810297161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36447994138156104540198107 54671991207234156810297161)
    ·
      refine ⟨41003993405425617607722871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54671991207234156810297161 41003993405425617607722871)
      ·
        refine ⟨61505990108138426411584307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41003993405425617607722871 61505990108138426411584307)
        ·
          refine ⟨92258985162207639617376461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61505990108138426411584307 92258985162207639617376461)
          ·
            refine ⟨34597119435827864856516173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92258985162207639617376461 34597119435827864856516173)
            ·
              refine ⟨12973919788435449321193565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34597119435827864856516173 12973919788435449321193565)
              ·
                refine ⟨4865219920663293495447587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12973919788435449321193565 4865219920663293495447587)
                ·
                  refine ⟨7297829880994940243171381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865219920663293495447587 7297829880994940243171381)
                  ·
                    refine ⟨684171551343275647797317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7297829880994940243171381 684171551343275647797317)
                    ·
                      rfl

theorem cell23_3997258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_3997258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997258 prefixEnd_3997258 := by exact prefixLift 3997258
  have htrace : WordTrace (prefixWord ++ tailWord_3997258) baseStart_3997258 baseEnd_3997258 := by
    simpa [prefixWord, tailWord_3997258, baseEnd_3997258] using wordTrace_append hprefix tailTrace_3997258
  have hstable : (prefixWord ++ tailWord_3997258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997258).length < 2 ^ (prefixWord ++ tailWord_3997258).sum := by decide
  have hdescent : baseEnd_3997258 < baseStart_3997258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997346 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3997346 : Nat := 118140960795 + 3997346 * 2 ^ 59
def prefixEnd_3997346 : Nat := 4983230072969 + 3 ^ 40 * 3997346 * 2
def baseEnd_3997346 : Nat := 2052559840327422599091547

theorem tailTrace_3997346 : CollatzResearch.WordTrace tailWord_3997346 prefixEnd_3997346 2052559840327422599091547 := by
  unfold tailWord_3997346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36448796544076402297498973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97196790784203739459997261 36448796544076402297498973)
  ·
    refine ⟨13668298704028650861562115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36448796544076402297498973 13668298704028650861562115)
    ·
      refine ⟨20502448056042976292343173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13668298704028650861562115 20502448056042976292343173)
      ·
        refine ⟨3844209010508058054814345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20502448056042976292343173 3844209010508058054814345)
        ·
          refine ⟨2883156757881043541110759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3844209010508058054814345 2883156757881043541110759)
          ·
            refine ⟨4324735136821565311666139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883156757881043541110759 4324735136821565311666139)
            ·
              refine ⟨6487102705232347967499209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4324735136821565311666139 6487102705232347967499209)
              ·
                refine ⟨4865327028924260975624407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6487102705232347967499209 4865327028924260975624407)
                ·
                  refine ⟨7297990543386391463436611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865327028924260975624407 7297990543386391463436611)
                  ·
                    refine ⟨10946985815079587195154917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7297990543386391463436611 10946985815079587195154917)
                    ·
                      refine ⟨2052559840327422599091547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10946985815079587195154917 2052559840327422599091547)
                      ·
                        rfl

theorem cell23_3997346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3997346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997346 prefixEnd_3997346 := by exact prefixLift 3997346
  have htrace : WordTrace (prefixWord ++ tailWord_3997346) baseStart_3997346 baseEnd_3997346 := by
    simpa [prefixWord, tailWord_3997346, baseEnd_3997346] using wordTrace_append hprefix tailTrace_3997346
  have hstable : (prefixWord ++ tailWord_3997346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997346).length < 2 ^ (prefixWord ++ tailWord_3997346).sum := by decide
  have hdescent : baseEnd_3997346 < baseStart_3997346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997366 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3997366 : Nat := 118140960795 + 3997366 * 2 ^ 59
def prefixEnd_3997366 : Nat := 4983230072969 + 3 ^ 40 * 3997366 * 2
def baseEnd_3997366 : Nat := 2052570109940512520841455

theorem tailTrace_3997366 : CollatzResearch.WordTrace tailWord_3997366 prefixEnd_3997366 2052570109940512520841455 := by
  unfold tailWord_3997366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9112244727264572037857747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97197277090822101737149301 9112244727264572037857747)
  ·
    refine ⟨13668367090896858056786621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9112244727264572037857747 13668367090896858056786621)
    ·
      refine ⟨5125637659086321771294983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13668367090896858056786621 5125637659086321771294983)
      ·
        refine ⟨7688456488629482656942475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125637659086321771294983 7688456488629482656942475)
        ·
          refine ⟨11532684732944223985413713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688456488629482656942475 11532684732944223985413713)
          ·
            refine ⟨8649513549708167989060285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11532684732944223985413713 8649513549708167989060285)
            ·
              refine ⟨3243567581140562995897607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8649513549708167989060285 3243567581140562995897607)
              ·
                refine ⟨4865351371710844493846411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243567581140562995897607 4865351371710844493846411)
                ·
                  refine ⟨7298027057566266740769617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4865351371710844493846411 7298027057566266740769617)
                  ·
                    refine ⟨5473520293174700055577213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7298027057566266740769617 5473520293174700055577213)
                    ·
                      refine ⟨2052570109940512520841455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5473520293174700055577213 2052570109940512520841455)
                      ·
                        rfl

theorem cell23_3997366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3997366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997366 prefixEnd_3997366 := by exact prefixLift 3997366
  have htrace : WordTrace (prefixWord ++ tailWord_3997366) baseStart_3997366 baseEnd_3997366 := by
    simpa [prefixWord, tailWord_3997366, baseEnd_3997366] using wordTrace_append hprefix tailTrace_3997366
  have hstable : (prefixWord ++ tailWord_3997366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997366).length < 2 ^ (prefixWord ++ tailWord_3997366).sum := by decide
  have hdescent : baseEnd_3997366 < baseStart_3997366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997382 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3997382 : Nat := 118140960795 + 3997382 * 2 ^ 59
def prefixEnd_3997382 : Nat := 4983230072969 + 3 ^ 40 * 3997382 * 2
def baseEnd_3997382 : Nat := 684192775210328152747127

theorem tailTrace_3997382 : CollatzResearch.WordTrace tailWord_3997382 prefixEnd_3997382 684192775210328152747127 := by
  unfold tailWord_3997382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4556140600130474604322075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97197666136116791558870933 4556140600130474604322075)
  ·
    refine ⟨6834210900195711906483113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4556140600130474604322075 6834210900195711906483113)
    ·
      refine ⟨5125658175146783929862335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834210900195711906483113 5125658175146783929862335)
      ·
        refine ⟨7688487262720175894793503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125658175146783929862335 7688487262720175894793503)
        ·
          refine ⟨11532730894080263842190255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688487262720175894793503 11532730894080263842190255)
          ·
            refine ⟨17299096341120395763285383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532730894080263842190255 17299096341120395763285383)
            ·
              refine ⟨25948644511680593644928075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299096341120395763285383 25948644511680593644928075)
              ·
                refine ⟨38922966767520890467392113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25948644511680593644928075 38922966767520890467392113)
                ·
                  refine ⟨29192225075640667850544085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38922966767520890467392113 29192225075640667850544085)
                  ·
                    refine ⟨684192775210328152747127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29192225075640667850544085 684192775210328152747127)
                    ·
                      rfl

theorem cell23_3997382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3997382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997382 prefixEnd_3997382 := by exact prefixLift 3997382
  have htrace : WordTrace (prefixWord ++ tailWord_3997382) baseStart_3997382 baseEnd_3997382 := by
    simpa [prefixWord, tailWord_3997382, baseEnd_3997382] using wordTrace_append hprefix tailTrace_3997382
  have hstable : (prefixWord ++ tailWord_3997382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997382).length < 2 ^ (prefixWord ++ tailWord_3997382).sum := by decide
  have hdescent : baseEnd_3997382 < baseStart_3997382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997389 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3997389 : Nat := 118140960795 + 3997389 * 2 ^ 59
def prefixEnd_3997389 : Nat := 4983230072969 + 3 ^ 40 * 3997389 * 2
def baseEnd_3997389 : Nat := 2052581919995565930853849

theorem tailTrace_3997389 : CollatzResearch.WordTrace tailWord_3997389 prefixEnd_3997389 2052581919995565930853849 := by
  unfold tailWord_3997389
  simp only [CollatzResearch.WordTrace]
  refine ⟨145796754515149827533811221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97197836343433218355874147 145796754515149827533811221)
  ·
    refine ⟨6834222867897648165647401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145796754515149827533811221 6834222867897648165647401)
    ·
      refine ⟨5125667150923236124235551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6834222867897648165647401 5125667150923236124235551)
      ·
        refine ⟨7688500726384854186353327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5125667150923236124235551 7688500726384854186353327)
        ·
          refine ⟨11532751089577281279529991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7688500726384854186353327 11532751089577281279529991)
          ·
            refine ⟨17299126634365921919294987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11532751089577281279529991 17299126634365921919294987)
            ·
              refine ⟨25948689951548882878942481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17299126634365921919294987 25948689951548882878942481)
              ·
                refine ⟨19461517463661662159206861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25948689951548882878942481 19461517463661662159206861)
                ·
                  refine ⟨7298069048873123309702573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19461517463661662159206861 7298069048873123309702573)
                  ·
                    refine ⟨2736775893327421241138465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7298069048873123309702573 2736775893327421241138465)
                    ·
                      refine ⟨2052581919995565930853849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736775893327421241138465 2052581919995565930853849)
                      ·
                        rfl

theorem cell23_3997389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3997389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997389 prefixEnd_3997389 := by exact prefixLift 3997389
  have htrace : WordTrace (prefixWord ++ tailWord_3997389) baseStart_3997389 baseEnd_3997389 := by
    simpa [prefixWord, tailWord_3997389, baseEnd_3997389] using wordTrace_append hprefix tailTrace_3997389
  have hstable : (prefixWord ++ tailWord_3997389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997389).length < 2 ^ (prefixWord ++ tailWord_3997389).sum := by decide
  have hdescent : baseEnd_3997389 < baseStart_3997389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997391 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 11]
def baseStart_3997391 : Nat := 118140960795 + 3997391 * 2 ^ 59
def prefixEnd_3997391 : Nat := 4983230072969 + 3 ^ 40 * 3997391 * 2
def baseEnd_3997391 : Nat := 228064771884097213669871

theorem tailTrace_3997391 : CollatzResearch.WordTrace tailWord_3997391 prefixEnd_3997391 228064771884097213669871 := by
  unfold tailWord_3997391
  simp only [CollatzResearch.WordTrace]
  refine ⟨145796827461142581875384027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97197884974095054583589351 145796827461142581875384027)
  ·
    refine ⟨218695241191713872813076041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145796827461142581875384027 218695241191713872813076041)
    ·
      refine ⟨164021430893785404609807031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218695241191713872813076041 164021430893785404609807031)
      ·
        refine ⟨246032146340678106914710547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164021430893785404609807031 246032146340678106914710547)
        ·
          refine ⟨369048219511017160372065821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246032146340678106914710547 369048219511017160372065821)
          ·
            refine ⟨138393082316631435139524683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369048219511017160372065821 138393082316631435139524683)
            ·
              refine ⟨207589623474947152709287025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138393082316631435139524683 207589623474947152709287025)
              ·
                refine ⟨155692217606210364531965269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207589623474947152709287025 155692217606210364531965269)
                ·
                  refine ⟨228064771884097213669871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 155692217606210364531965269 228064771884097213669871)
                  ·
                    rfl

theorem cell23_3997391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 11].length) (baseStart_3997391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997391 prefixEnd_3997391 := by exact prefixLift 3997391
  have htrace : WordTrace (prefixWord ++ tailWord_3997391) baseStart_3997391 baseEnd_3997391 := by
    simpa [prefixWord, tailWord_3997391, baseEnd_3997391] using wordTrace_append hprefix tailTrace_3997391
  have hstable : (prefixWord ++ tailWord_3997391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997391).length < 2 ^ (prefixWord ++ tailWord_3997391).sum := by decide
  have hdescent : baseEnd_3997391 < baseStart_3997391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3997402 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_3997402 : Nat := 118140960795 + 3997402 * 2 ^ 59
def prefixEnd_3997402 : Nat := 4983230072969 + 3 ^ 40 * 3997402 * 2
def baseEnd_3997402 : Nat := 2052588595244074379991289

theorem tailTrace_3997402 : CollatzResearch.WordTrace tailWord_3997402 prefixEnd_3997402 2052588595244074379991289 := by
  unfold tailWord_3997402
  simp only [CollatzResearch.WordTrace]
  refine ⟨36449307166025682688508615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97198152442735153836022973 36449307166025682688508615)
  ·
    refine ⟨54673960749038524032762923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36449307166025682688508615 54673960749038524032762923)
    ·
      refine ⟨82010941123557786049144385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54673960749038524032762923 82010941123557786049144385)
      ·
        refine ⟨61508205842668339536858289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82010941123557786049144385 61508205842668339536858289)
        ·
          refine ⟨46131154382001254652643717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61508205842668339536858289 46131154382001254652643717)
          ·
            refine ⟨8649591446625235247370697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46131154382001254652643717 8649591446625235247370697)
            ·
              refine ⟨6487193584968926435528023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8649591446625235247370697 6487193584968926435528023)
              ·
                refine ⟨9730790377453389653292035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6487193584968926435528023 9730790377453389653292035)
                ·
                  refine ⟨14596185566180084479938053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9730790377453389653292035 14596185566180084479938053)
                  ·
                    refine ⟨2736784793658765839988385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14596185566180084479938053 2736784793658765839988385)
                    ·
                      refine ⟨2052588595244074379991289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2736784793658765839988385 2052588595244074379991289)
                      ·
                        rfl

theorem cell23_3997402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_3997402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3997402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3997402 prefixEnd_3997402 := by exact prefixLift 3997402
  have htrace : WordTrace (prefixWord ++ tailWord_3997402) baseStart_3997402 baseEnd_3997402 := by
    simpa [prefixWord, tailWord_3997402, baseEnd_3997402] using wordTrace_append hprefix tailTrace_3997402
  have hstable : (prefixWord ++ tailWord_3997402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3997402).length < 2 ^ (prefixWord ++ tailWord_3997402).sum := by decide
  have hdescent : baseEnd_3997402 < baseStart_3997402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3997402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
