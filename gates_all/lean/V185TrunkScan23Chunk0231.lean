import V185TrunkScan23Chunk0230

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1365665 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1365665 : Nat := 118140960795 + 1365665 * 2 ^ 59
def prefixEnd_1365665 : Nat := 4983230072969 + 3 ^ 40 * 1365665 * 2
def baseEnd_1365665 : Nat := 701242558022504563106927

theorem tailTrace_1365665 : CollatzResearch.WordTrace tailWord_1365665 prefixEnd_1365665 701242558022504563106927 := by
  unfold tailWord_1365665
  simp only [CollatzResearch.WordTrace]
  refine ⟨49809894597436416858162449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33206596398290944572108299 49809894597436416858162449)
  ·
    refine ⟨37357420948077312643621837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49809894597436416858162449 37357420948077312643621837)
    ·
      refine ⟨14009032855528992241358189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37357420948077312643621837 14009032855528992241358189)
      ·
        refine ⟨5253387320823372090509321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14009032855528992241358189 5253387320823372090509321)
        ·
          refine ⟨3940040490617529067881991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253387320823372090509321 3940040490617529067881991)
          ·
            refine ⟨5910060735926293601822987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940040490617529067881991 5910060735926293601822987)
            ·
              refine ⟨8865091103889440402734481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910060735926293601822987 8865091103889440402734481)
              ·
                refine ⟨6648818327917080302050861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8865091103889440402734481 6648818327917080302050861)
                ·
                  refine ⟨2493306872968905113269073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6648818327917080302050861 2493306872968905113269073)
                  ·
                    refine ⟨1869980154726678834951805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493306872968905113269073 1869980154726678834951805)
                    ·
                      refine ⟨701242558022504563106927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1869980154726678834951805 701242558022504563106927)
                      ·
                        rfl

theorem cell23_1365665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1365665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365665 prefixEnd_1365665 := by exact prefixLift 1365665
  have htrace : WordTrace (prefixWord ++ tailWord_1365665) baseStart_1365665 baseEnd_1365665 := by
    simpa [prefixWord, tailWord_1365665, baseEnd_1365665] using wordTrace_append hprefix tailTrace_1365665
  have hstable : (prefixWord ++ tailWord_1365665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365665).length < 2 ^ (prefixWord ++ tailWord_1365665).sum := by decide
  have hdescent : baseEnd_1365665 < baseStart_1365665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365668 : List Nat := [2, 3, 1, 2, 2, 2, 3, 8]
def baseStart_1365668 : Nat := 118140960795 + 1365668 * 2 ^ 59
def prefixEnd_1365668 : Nat := 4983230072969 + 3 ^ 40 * 1365668 * 2
def baseEnd_1365668 : Nat := 25972003646832150050719

theorem tailTrace_1365668 : CollatzResearch.WordTrace tailWord_1365668 prefixEnd_1365668 25972003646832150050719 := by
  unfold tailWord_1365668
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905002008212774185260829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33206669344283698913681105 24905002008212774185260829)
  ·
    refine ⟨9339375753079790319472811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24905002008212774185260829 9339375753079790319472811)
    ·
      refine ⟨14009063629619685479209217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9339375753079790319472811 14009063629619685479209217)
      ·
        refine ⟨10506797722214764109406913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14009063629619685479209217 10506797722214764109406913)
        ·
          refine ⟨7880098291661073082055185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10506797722214764109406913 7880098291661073082055185)
          ·
            refine ⟨5910073718745804811541389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7880098291661073082055185 5910073718745804811541389)
            ·
              refine ⟨2216277644529676804328021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5910073718745804811541389 2216277644529676804328021)
              ·
                refine ⟨25972003646832150050719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2216277644529676804328021 25972003646832150050719)
                ·
                  rfl

theorem cell23_1365668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 8].length) (baseStart_1365668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365668 prefixEnd_1365668 := by exact prefixLift 1365668
  have htrace : WordTrace (prefixWord ++ tailWord_1365668) baseStart_1365668 baseEnd_1365668 := by
    simpa [prefixWord, tailWord_1365668, baseEnd_1365668] using wordTrace_append hprefix tailTrace_1365668
  have hstable : (prefixWord ++ tailWord_1365668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365668).length < 2 ^ (prefixWord ++ tailWord_1365668).sum := by decide
  have hdescent : baseEnd_1365668 < baseStart_1365668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365695 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 3]
def baseStart_1365695 : Nat := 118140960795 + 1365695 * 2 ^ 59
def prefixEnd_1365695 : Nat := 4983230072969 + 3 ^ 40 * 1365695 * 2
def baseEnd_1365695 : Nat := 701257962442139445731789

theorem tailTrace_1365695 : CollatzResearch.WordTrace tailWord_1365695 prefixEnd_1365695 701257962442139445731789 := by
  unfold tailWord_1365695
  simp only [CollatzResearch.WordTrace]
  refine ⟨49810988787327731981754539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33207325858218487987836359 49810988787327731981754539)
  ·
    refine ⟨74716483180991597972631809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49810988787327731981754539 74716483180991597972631809)
    ·
      refine ⟨56037362385743698479473857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74716483180991597972631809 56037362385743698479473857)
      ·
        refine ⟨42028021789307773859605393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56037362385743698479473857 42028021789307773859605393)
        ·
          refine ⟨31521016341980830394704045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42028021789307773859605393 31521016341980830394704045)
          ·
            refine ⟨11820381128242811398014017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31521016341980830394704045 11820381128242811398014017)
            ·
              refine ⟨8865285846182108548510513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11820381128242811398014017 8865285846182108548510513)
              ·
                refine ⟨6648964384636581411382885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8865285846182108548510513 6648964384636581411382885)
                ·
                  refine ⟨1246680822119359014634291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6648964384636581411382885 1246680822119359014634291)
                  ·
                    refine ⟨1870021233179038521951437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1246680822119359014634291 1870021233179038521951437)
                    ·
                      refine ⟨701257962442139445731789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1870021233179038521951437 701257962442139445731789)
                      ·
                        rfl

theorem cell23_1365695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_1365695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365695 prefixEnd_1365695 := by exact prefixLift 1365695
  have htrace : WordTrace (prefixWord ++ tailWord_1365695) baseStart_1365695 baseEnd_1365695 := by
    simpa [prefixWord, tailWord_1365695, baseEnd_1365695] using wordTrace_append hprefix tailTrace_1365695
  have hstable : (prefixWord ++ tailWord_1365695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365695).length < 2 ^ (prefixWord ++ tailWord_1365695).sum := by decide
  have hdescent : baseEnd_1365695 < baseStart_1365695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365702 : List Nat := [6, 1, 2, 1, 1, 2, 10]
def baseStart_1365702 : Nat := 118140960795 + 1365702 * 2 ^ 59
def prefixEnd_1365702 : Nat := 4983230072969 + 3 ^ 40 * 1365702 * 2
def baseEnd_1365702 : Nat := 8657550084033591584497

theorem tailTrace_1365702 : CollatzResearch.WordTrace tailWord_1365702 prefixEnd_1365702 8657550084033591584497 := by
  unfold tailWord_1365702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556601378071949130539355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33207496065534914784839573 1556601378071949130539355)
  ·
    refine ⟨2334902067107923695809033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556601378071949130539355 2334902067107923695809033)
    ·
      refine ⟨1751176550330942771856775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334902067107923695809033 1751176550330942771856775)
      ·
        refine ⟨2626764825496414157785163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751176550330942771856775 2626764825496414157785163)
        ·
          refine ⟨3940147238244621236677745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626764825496414157785163 3940147238244621236677745)
          ·
            refine ⟨2955110428683465927508309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3940147238244621236677745 2955110428683465927508309)
            ·
              refine ⟨8657550084033591584497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2955110428683465927508309 8657550084033591584497)
              ·
                rfl

theorem cell23_1365702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 10].length) (baseStart_1365702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365702 prefixEnd_1365702 := by exact prefixLift 1365702
  have htrace : WordTrace (prefixWord ++ tailWord_1365702) baseStart_1365702 baseEnd_1365702 := by
    simpa [prefixWord, tailWord_1365702, baseEnd_1365702] using wordTrace_append hprefix tailTrace_1365702
  have hstable : (prefixWord ++ tailWord_1365702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365702).length < 2 ^ (prefixWord ++ tailWord_1365702).sum := by decide
  have hdescent : baseEnd_1365702 < baseStart_1365702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365728 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_1365728 : Nat := 118140960795 + 1365728 * 2 ^ 59
def prefixEnd_1365728 : Nat := 4983230072969 + 3 ^ 40 * 1365728 * 2
def baseEnd_1365728 : Nat := 233758302434579272206379

theorem tailTrace_1365728 : CollatzResearch.WordTrace tailWord_1365728 prefixEnd_1365728 233758302434579272206379 := by
  unfold tailWord_1365728
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906096198104089308852919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33208128264138785745137225 24906096198104089308852919)
  ·
    refine ⟨37359144297156133963279379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24906096198104089308852919 37359144297156133963279379)
    ·
      refine ⟨56038716445734200944919069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37359144297156133963279379 56038716445734200944919069)
      ·
        refine ⟨21014518667150325354344651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56038716445734200944919069 21014518667150325354344651)
        ·
          refine ⟨31521778000725488031516977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21014518667150325354344651 31521778000725488031516977)
          ·
            refine ⟨23641333500544116023637733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31521778000725488031516977 23641333500544116023637733)
            ·
              refine ⟨4432750031352021754432075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23641333500544116023637733 4432750031352021754432075)
              ·
                refine ⟨6649125047028032631648113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432750031352021754432075 6649125047028032631648113)
                ·
                  refine ⟨4986843785271024473736085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6649125047028032631648113 4986843785271024473736085)
                  ·
                    refine ⟨233758302434579272206379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4986843785271024473736085 233758302434579272206379)
                    ·
                      rfl

theorem cell23_1365728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_1365728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365728 prefixEnd_1365728 := by exact prefixLift 1365728
  have htrace : WordTrace (prefixWord ++ tailWord_1365728) baseStart_1365728 baseEnd_1365728 := by
    simpa [prefixWord, tailWord_1365728, baseEnd_1365728] using wordTrace_append hprefix tailTrace_1365728
  have hstable : (prefixWord ++ tailWord_1365728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365728).length < 2 ^ (prefixWord ++ tailWord_1365728).sum := by decide
  have hdescent : baseEnd_1365728 < baseStart_1365728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365729 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_1365729 : Nat := 118140960795 + 1365729 * 2 ^ 59
def prefixEnd_1365729 : Nat := 4983230072969 + 3 ^ 40 * 1365729 * 2
def baseEnd_1365729 : Nat := 701275420784392312706633

theorem tailTrace_1365729 : CollatzResearch.WordTrace tailWord_1365729 prefixEnd_1365729 701275420784392312706633 := by
  unfold tailWord_1365729
  simp only [CollatzResearch.WordTrace]
  refine ⟨49812228869204555788492241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33208152579469703858994827 49812228869204555788492241)
  ·
    refine ⟨37359171651903416841369181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49812228869204555788492241 37359171651903416841369181)
    ·
      refine ⟨14009689369463781315513443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37359171651903416841369181 14009689369463781315513443)
      ·
        refine ⟨21014534054195671973270165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14009689369463781315513443 21014534054195671973270165)
        ·
          refine ⟨985056283790422123747039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21014534054195671973270165 985056283790422123747039)
          ·
            refine ⟨1477584425685633185620559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985056283790422123747039 1477584425685633185620559)
            ·
              refine ⟨2216376638528449778430839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477584425685633185620559 2216376638528449778430839)
              ·
                refine ⟨3324564957792674667646259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216376638528449778430839 3324564957792674667646259)
                ·
                  refine ⟨4986847436689012001469389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324564957792674667646259 4986847436689012001469389)
                  ·
                    refine ⟨1870067788758379500551021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4986847436689012001469389 1870067788758379500551021)
                    ·
                      refine ⟨701275420784392312706633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1870067788758379500551021 701275420784392312706633)
                      ·
                        rfl

theorem cell23_1365729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_1365729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365729 prefixEnd_1365729 := by exact prefixLift 1365729
  have htrace : WordTrace (prefixWord ++ tailWord_1365729) baseStart_1365729 baseEnd_1365729 := by
    simpa [prefixWord, tailWord_1365729, baseEnd_1365729] using wordTrace_append hprefix tailTrace_1365729
  have hstable : (prefixWord ++ tailWord_1365729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365729).length < 2 ^ (prefixWord ++ tailWord_1365729).sum := by decide
  have hdescent : baseEnd_1365729 < baseStart_1365729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365768 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1365768 : Nat := 118140960795 + 1365768 * 2 ^ 59
def prefixEnd_1365768 : Nat := 4983230072969 + 3 ^ 40 * 1365768 * 2
def baseEnd_1365768 : Nat := 701295446529917660118953

theorem tailTrace_1365768 : CollatzResearch.WordTrace tailWord_1365768 prefixEnd_1365768 701295446529917660118953 := by
  unfold tailWord_1365768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24906825658031632724580979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33209100877375510299441305 24906825658031632724580979)
  ·
    refine ⟨37360238487047449086871469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24906825658031632724580979 37360238487047449086871469)
    ·
      refine ⟨14010089432642793407576801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37360238487047449086871469 14010089432642793407576801)
      ·
        refine ⟨10507567074482095055682601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14010089432642793407576801 10507567074482095055682601)
        ·
          refine ⟨7880675305861571291761951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10507567074482095055682601 7880675305861571291761951)
          ·
            refine ⟨11821012958792356937642927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880675305861571291761951 11821012958792356937642927)
            ·
              refine ⟨17731519438188535406464391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11821012958792356937642927 17731519438188535406464391)
              ·
                refine ⟨26597279157282803109696587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17731519438188535406464391 26597279157282803109696587)
                ·
                  refine ⟨39895918735924204664544881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26597279157282803109696587 39895918735924204664544881)
                  ·
                    refine ⟨29921939051943153498408661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39895918735924204664544881 29921939051943153498408661)
                    ·
                      refine ⟨701295446529917660118953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29921939051943153498408661 701295446529917660118953)
                      ·
                        rfl

theorem cell23_1365768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1365768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365768 prefixEnd_1365768 := by exact prefixLift 1365768
  have htrace : WordTrace (prefixWord ++ tailWord_1365768) baseStart_1365768 baseEnd_1365768 := by
    simpa [prefixWord, tailWord_1365768, baseEnd_1365768] using wordTrace_append hprefix tailTrace_1365768
  have hstable : (prefixWord ++ tailWord_1365768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365768).length < 2 ^ (prefixWord ++ tailWord_1365768).sum := by decide
  have hdescent : baseEnd_1365768 < baseStart_1365768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365786 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_1365786 : Nat := 118140960795 + 1365786 * 2 ^ 59
def prefixEnd_1365786 : Nat := 4983230072969 + 3 ^ 40 * 1365786 * 2
def baseEnd_1365786 : Nat := 701304689181698589693871

theorem tailTrace_1365786 : CollatzResearch.WordTrace tailWord_1365786 prefixEnd_1365786 701304689181698589693871 := by
  unfold tailWord_1365786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12453576957499513630829303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33209538553332036348878141 12453576957499513630829303)
  ·
    refine ⟨18680365436249270446243955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12453576957499513630829303 18680365436249270446243955)
    ·
      refine ⟨28020548154373905669365933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18680365436249270446243955 28020548154373905669365933)
      ·
        refine ⟨10507705557890214626012225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28020548154373905669365933 10507705557890214626012225)
        ·
          refine ⟨7880779168417660969509169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10507705557890214626012225 7880779168417660969509169)
          ·
            refine ⟨5910584376313245727131877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7880779168417660969509169 5910584376313245727131877)
            ·
              refine ⟨1108234570558733573837227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5910584376313245727131877 1108234570558733573837227)
              ·
                refine ⟨1662351855838100360755841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108234570558733573837227 1662351855838100360755841)
                ·
                  refine ⟨1246763891878575270566881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1662351855838100360755841 1246763891878575270566881)
                  ·
                    refine ⟨935072918908931452925161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1246763891878575270566881 935072918908931452925161)
                    ·
                      refine ⟨701304689181698589693871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935072918908931452925161 701304689181698589693871)
                      ·
                        rfl

theorem cell23_1365786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_1365786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365786 prefixEnd_1365786 := by exact prefixLift 1365786
  have htrace : WordTrace (prefixWord ++ tailWord_1365786) baseStart_1365786 baseEnd_1365786 := by
    simpa [prefixWord, tailWord_1365786, baseEnd_1365786] using wordTrace_append hprefix tailTrace_1365786
  have hstable : (prefixWord ++ tailWord_1365786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365786).length < 2 ^ (prefixWord ++ tailWord_1365786).sum := by decide
  have hdescent : baseEnd_1365786 < baseStart_1365786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365790 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1365790 : Nat := 118140960795 + 1365790 * 2 ^ 59
def prefixEnd_1365790 : Nat := 4983230072969 + 3 ^ 40 * 1365790 * 2
def baseEnd_1365790 : Nat := 701306743104316574043853

theorem tailTrace_1365790 : CollatzResearch.WordTrace tailWord_1365790 prefixEnd_1365790 701306743104316574043853 := by
  unfold tailWord_1365790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226806715247945400807853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33209635814655708804308549 6226806715247945400807853)
  ·
    refine ⟨2335052518217979525302945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6226806715247945400807853 2335052518217979525302945)
    ·
      refine ⟨1751289388663484643977209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2335052518217979525302945 1751289388663484643977209)
      ·
        refine ⟨1313467041497613482982907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1751289388663484643977209 1313467041497613482982907)
        ·
          refine ⟨1970200562246420224474361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313467041497613482982907 1970200562246420224474361)
          ·
            refine ⟨1477650421684815168355771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970200562246420224474361 1477650421684815168355771)
            ·
              refine ⟨2216475632527222752533657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477650421684815168355771 2216475632527222752533657)
              ·
                refine ⟨1662356724395417064400243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2216475632527222752533657 1662356724395417064400243)
                ·
                  refine ⟨2493535086593125596600365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662356724395417064400243 2493535086593125596600365)
                  ·
                    refine ⟨935075657472422098725137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493535086593125596600365 935075657472422098725137)
                    ·
                      refine ⟨701306743104316574043853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935075657472422098725137 701306743104316574043853)
                      ·
                        rfl

theorem cell23_1365790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1365790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365790 prefixEnd_1365790 := by exact prefixLift 1365790
  have htrace : WordTrace (prefixWord ++ tailWord_1365790) baseStart_1365790 baseEnd_1365790 := by
    simpa [prefixWord, tailWord_1365790, baseEnd_1365790] using wordTrace_append hprefix tailTrace_1365790
  have hstable : (prefixWord ++ tailWord_1365790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365790).length < 2 ^ (prefixWord ++ tailWord_1365790).sum := by decide
  have hdescent : baseEnd_1365790 < baseStart_1365790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365822 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1365822 : Nat := 118140960795 + 1365822 * 2 ^ 59
def prefixEnd_1365822 : Nat := 4983230072969 + 3 ^ 40 * 1365822 * 2
def baseEnd_1365822 : Nat := 233774391495086816281235

theorem tailTrace_1365822 : CollatzResearch.WordTrace tailWord_1365822 prefixEnd_1365822 233774391495086816281235 := by
  unfold tailWord_1365822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226952607233454083953465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33210413905245088447751813 6226952607233454083953465)
  ·
    refine ⟨4670214455425090562965099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6226952607233454083953465 4670214455425090562965099)
    ·
      refine ⟨7005321683137635844447649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670214455425090562965099 7005321683137635844447649)
      ·
        refine ⟨5253991262353226883335737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7005321683137635844447649 5253991262353226883335737)
        ·
          refine ⟨3940493446764920162501803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253991262353226883335737 3940493446764920162501803)
          ·
            refine ⟨5910740170147380243752705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940493446764920162501803 5910740170147380243752705)
            ·
              refine ⟨4433055127610535182814529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5910740170147380243752705 4433055127610535182814529)
              ·
                refine ⟨3324791345707901387110897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4433055127610535182814529 3324791345707901387110897)
                ·
                  refine ⟨2493593509280926040333173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324791345707901387110897 2493593509280926040333173)
                  ·
                    refine ⟨233774391495086816281235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2493593509280926040333173 233774391495086816281235)
                    ·
                      rfl

theorem cell23_1365822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1365822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365822 prefixEnd_1365822 := by exact prefixLift 1365822
  have htrace : WordTrace (prefixWord ++ tailWord_1365822) baseStart_1365822 baseEnd_1365822 := by
    simpa [prefixWord, tailWord_1365822, baseEnd_1365822] using wordTrace_append hprefix tailTrace_1365822
  have hstable : (prefixWord ++ tailWord_1365822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365822).length < 2 ^ (prefixWord ++ tailWord_1365822).sum := by decide
  have hdescent : baseEnd_1365822 < baseStart_1365822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365842 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_1365842 : Nat := 118140960795 + 1365842 * 2 ^ 59
def prefixEnd_1365842 : Nat := 4983230072969 + 3 ^ 40 * 1365842 * 2
def baseEnd_1365842 : Nat := 701333444098350370593613

theorem tailTrace_1365842 : CollatzResearch.WordTrace tailWord_1365842 prefixEnd_1365842 701333444098350370593613 := by
  unfold tailWord_1365842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454087579448794021838945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33210900211863450724903853 12454087579448794021838945)
  ·
    refine ⟨9340565684586595516379209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12454087579448794021838945 9340565684586595516379209)
    ·
      refine ⟨7005424263439946637284407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9340565684586595516379209 7005424263439946637284407)
      ·
        refine ⟨10508136395159919955926611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005424263439946637284407 10508136395159919955926611)
        ·
          refine ⟨15762204592739879933889917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10508136395159919955926611 15762204592739879933889917)
          ·
            refine ⟨5910826722277454975208719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15762204592739879933889917 5910826722277454975208719)
            ·
              refine ⟨8866240083416182462813079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910826722277454975208719 8866240083416182462813079)
              ·
                refine ⟨13299360125124273694219619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8866240083416182462813079 13299360125124273694219619)
                ·
                  refine ⟨19949040187686410541329429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13299360125124273694219619 19949040187686410541329429)
                  ·
                    refine ⟨935111258797800494124817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19949040187686410541329429 935111258797800494124817)
                    ·
                      refine ⟨701333444098350370593613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935111258797800494124817 701333444098350370593613)
                      ·
                        rfl

theorem cell23_1365842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_1365842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365842 prefixEnd_1365842 := by exact prefixLift 1365842
  have htrace : WordTrace (prefixWord ++ tailWord_1365842) baseStart_1365842 baseEnd_1365842 := by
    simpa [prefixWord, tailWord_1365842, baseEnd_1365842] using wordTrace_append hprefix tailTrace_1365842
  have hstable : (prefixWord ++ tailWord_1365842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365842).length < 2 ^ (prefixWord ++ tailWord_1365842).sum := by decide
  have hdescent : baseEnd_1365842 < baseStart_1365842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365848 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 12]
def baseStart_1365848 : Nat := 118140960795 + 1365848 * 2 ^ 59
def prefixEnd_1365848 : Nat := 4983230072969 + 3 ^ 40 * 1365848 * 2
def baseEnd_1365848 : Nat := 77926280553586371902065

theorem tailTrace_1365848 : CollatzResearch.WordTrace tailWord_1365848 prefixEnd_1365848 77926280553586371902065 := by
  unfold tailWord_1365848
  simp only [CollatzResearch.WordTrace]
  refine ⟨24908284577886719556037099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33211046103848959408049465 24908284577886719556037099)
  ·
    refine ⟨37362426866830079334055649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24908284577886719556037099 37362426866830079334055649)
    ·
      refine ⟨28021820150122559500541737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37362426866830079334055649 28021820150122559500541737)
      ·
        refine ⟨21016365112591919625406303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28021820150122559500541737 21016365112591919625406303)
        ·
          refine ⟨31524547668887879438109455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21016365112591919625406303 31524547668887879438109455)
          ·
            refine ⟨47286821503331819157164183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31524547668887879438109455 47286821503331819157164183)
            ·
              refine ⟨70930232254997728735746275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47286821503331819157164183 70930232254997728735746275)
              ·
                refine ⟨106395348382496593103619413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70930232254997728735746275 106395348382496593103619413)
                ·
                  refine ⟨77926280553586371902065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 106395348382496593103619413 77926280553586371902065)
                  ·
                    rfl

theorem cell23_1365848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_1365848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365848 prefixEnd_1365848 := by exact prefixLift 1365848
  have htrace : WordTrace (prefixWord ++ tailWord_1365848) baseStart_1365848 baseEnd_1365848 := by
    simpa [prefixWord, tailWord_1365848, baseEnd_1365848] using wordTrace_append hprefix tailTrace_1365848
  have hstable : (prefixWord ++ tailWord_1365848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365848).length < 2 ^ (prefixWord ++ tailWord_1365848).sum := by decide
  have hdescent : baseEnd_1365848 < baseStart_1365848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365859 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1365859 : Nat := 118140960795 + 1365859 * 2 ^ 59
def prefixEnd_1365859 : Nat := 4983230072969 + 3 ^ 40 * 1365859 * 2
def baseEnd_1365859 : Nat := 701342173269476804081035

theorem tailTrace_1365859 : CollatzResearch.WordTrace tailWord_1365859 prefixEnd_1365859 701342173269476804081035 := by
  unfold tailWord_1365859
  simp only [CollatzResearch.WordTrace]
  refine ⟨49816970358733587990724631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33211313572489058660483087 49816970358733587990724631)
  ·
    refine ⟨74725455538100381986086947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49816970358733587990724631 74725455538100381986086947)
    ·
      refine ⟨112088183307150572979130421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74725455538100381986086947 112088183307150572979130421)
      ·
        refine ⟨10508267185045366216793477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112088183307150572979130421 10508267185045366216793477)
        ·
          refine ⟨1970300097196006165648777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10508267185045366216793477 1970300097196006165648777)
          ·
            refine ⟨1477725072897004624236583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970300097196006165648777 1477725072897004624236583)
            ·
              refine ⟨2216587609345506936354875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477725072897004624236583 2216587609345506936354875)
              ·
                refine ⟨3324881414018260404532313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216587609345506936354875 3324881414018260404532313)
                ·
                  refine ⟨2493661060513695303399235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3324881414018260404532313 2493661060513695303399235)
                  ·
                    refine ⟨3740491590770542955098853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2493661060513695303399235 3740491590770542955098853)
                    ·
                      refine ⟨701342173269476804081035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3740491590770542955098853 701342173269476804081035)
                      ·
                        rfl

theorem cell23_1365859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1365859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365859 prefixEnd_1365859 := by exact prefixLift 1365859
  have htrace : WordTrace (prefixWord ++ tailWord_1365859) baseStart_1365859 baseEnd_1365859 := by
    simpa [prefixWord, tailWord_1365859, baseEnd_1365859] using wordTrace_append hprefix tailTrace_1365859
  have hstable : (prefixWord ++ tailWord_1365859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365859).length < 2 ^ (prefixWord ++ tailWord_1365859).sum := by decide
  have hdescent : baseEnd_1365859 < baseStart_1365859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365869 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1365869 : Nat := 118140960795 + 1365869 * 2 ^ 59
def prefixEnd_1365869 : Nat := 4983230072969 + 3 ^ 40 * 1365869 * 2
def baseEnd_1365869 : Nat := 233782436025340588318663

theorem tailTrace_1365869 : CollatzResearch.WordTrace tailWord_1365869 prefixEnd_1365869 233782436025340588318663 := by
  unfold tailWord_1365869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49817335088697359698588661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33211556725798239799059107 49817335088697359698588661)
  ·
    refine ⟨4670375164565377471742687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49817335088697359698588661 4670375164565377471742687)
    ·
      refine ⟨7005562746848066207614031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670375164565377471742687 7005562746848066207614031)
      ·
        refine ⟨10508344120272099311421047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7005562746848066207614031 10508344120272099311421047)
        ·
          refine ⟨15762516180408148967131571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10508344120272099311421047 15762516180408148967131571)
          ·
            refine ⟨23643774270612223450697357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15762516180408148967131571 23643774270612223450697357)
            ·
              refine ⟨8866415351479583794011509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23643774270612223450697357 8866415351479583794011509)
              ·
                refine ⟨831226439201210980688579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8866415351479583794011509 831226439201210980688579)
                ·
                  refine ⟨1246839658801816471032869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831226439201210980688579 1246839658801816471032869)
                  ·
                    refine ⟨233782436025340588318663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246839658801816471032869 233782436025340588318663)
                    ·
                      rfl

theorem cell23_1365869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1365869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365869 prefixEnd_1365869 := by exact prefixLift 1365869
  have htrace : WordTrace (prefixWord ++ tailWord_1365869) baseStart_1365869 baseEnd_1365869 := by
    simpa [prefixWord, tailWord_1365869, baseEnd_1365869] using wordTrace_append hprefix tailTrace_1365869
  have hstable : (prefixWord ++ tailWord_1365869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365869).length < 2 ^ (prefixWord ++ tailWord_1365869).sum := by decide
  have hdescent : baseEnd_1365869 < baseStart_1365869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365886 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1365886 : Nat := 118140960795 + 1365886 * 2 ^ 59
def prefixEnd_1365886 : Nat := 4983230072969 + 3 ^ 40 * 1365886 * 2
def baseEnd_1365886 : Nat := 233785345749049399481137

theorem tailTrace_1365886 : CollatzResearch.WordTrace tailWord_1365886 prefixEnd_1365886 233785345749049399481137 := by
  unfold tailWord_1365886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6227244391204471450244689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33211970086423847734638341 6227244391204471450244689)
  ·
    refine ⟨4670433293403353587683517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6227244391204471450244689 4670433293403353587683517)
    ·
      refine ⟨1751412485026257595381319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4670433293403353587683517 1751412485026257595381319)
      ·
        refine ⟨2627118727539386393071979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751412485026257595381319 2627118727539386393071979)
        ·
          refine ⟨3940678091309079589607969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627118727539386393071979 3940678091309079589607969)
          ·
            refine ⟨2955508568481809692205977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3940678091309079589607969 2955508568481809692205977)
            ·
              refine ⟨2216631426361357269154483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2955508568481809692205977 2216631426361357269154483)
              ·
                refine ⟨3324947139542035903731725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216631426361357269154483 3324947139542035903731725)
                ·
                  refine ⟨1246855177328263463899397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3324947139542035903731725 1246855177328263463899397)
                  ·
                    refine ⟨233785345749049399481137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1246855177328263463899397 233785345749049399481137)
                    ·
                      rfl

theorem cell23_1365886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1365886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365886 prefixEnd_1365886 := by exact prefixLift 1365886
  have htrace : WordTrace (prefixWord ++ tailWord_1365886) baseStart_1365886 baseEnd_1365886 := by
    simpa [prefixWord, tailWord_1365886, baseEnd_1365886] using wordTrace_append hprefix tailTrace_1365886
  have hstable : (prefixWord ++ tailWord_1365886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365886).length < 2 ^ (prefixWord ++ tailWord_1365886).sum := by decide
  have hdescent : baseEnd_1365886 < baseStart_1365886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365925 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_1365925 : Nat := 118140960795 + 1365925 * 2 ^ 59
def prefixEnd_1365925 : Nat := 4983230072969 + 3 ^ 40 * 1365925 * 2
def baseEnd_1365925 : Nat := 233792020997557848618577

theorem tailTrace_1365925 : CollatzResearch.WordTrace tailWord_1365925 prefixEnd_1365925 233792020997557848618577 := by
  unfold tailWord_1365925
  simp only [CollatzResearch.WordTrace]
  refine ⟨49819377576494481262627229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33212918384329654175084819 49819377576494481262627229)
  ·
    refine ⟨18682266591185430473485211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49819377576494481262627229 18682266591185430473485211)
    ·
      refine ⟨28023399886778145710227817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18682266591185430473485211 28023399886778145710227817)
      ·
        refine ⟨21017549915083609282670863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28023399886778145710227817 21017549915083609282670863)
        ·
          refine ⟨31526324872625413924006295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21017549915083609282670863 31526324872625413924006295)
          ·
            refine ⟨47289487308938120886009443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31526324872625413924006295 47289487308938120886009443)
            ·
              refine ⟨70934230963407181329014165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47289487308938120886009443 70934230963407181329014165)
              ·
                refine ⟨3325042076409711624797539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70934230963407181329014165 3325042076409711624797539)
                ·
                  refine ⟨4987563114614567437196309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325042076409711624797539 4987563114614567437196309)
                  ·
                    refine ⟨233792020997557848618577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4987563114614567437196309 233792020997557848618577)
                    ·
                      rfl

theorem cell23_1365925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_1365925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365925 prefixEnd_1365925 := by exact prefixLift 1365925
  have htrace : WordTrace (prefixWord ++ tailWord_1365925) baseStart_1365925 baseEnd_1365925 := by
    simpa [prefixWord, tailWord_1365925, baseEnd_1365925] using wordTrace_append hprefix tailTrace_1365925
  have hstable : (prefixWord ++ tailWord_1365925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365925).length < 2 ^ (prefixWord ++ tailWord_1365925).sum := by decide
  have hdescent : baseEnd_1365925 < baseStart_1365925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365945 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1365945 : Nat := 118140960795 + 1365945 * 2 ^ 59
def prefixEnd_1365945 : Nat := 4983230072969 + 3 ^ 40 * 1365945 * 2
def baseEnd_1365945 : Nat := 701386332605763467605639

theorem tailTrace_1365945 : CollatzResearch.WordTrace tailWord_1365945 prefixEnd_1365945 701386332605763467605639 := by
  unfold tailWord_1365945
  simp only [CollatzResearch.WordTrace]
  refine ⟨49820107036422024678355289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33213404690948016452236859 49820107036422024678355289)
  ·
    refine ⟨37365080277316518508766467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49820107036422024678355289 37365080277316518508766467)
    ·
      refine ⟨56047620415974777763149701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37365080277316518508766467 56047620415974777763149701)
      ·
        refine ⟨10508928827995270830590569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56047620415974777763149701 10508928827995270830590569)
        ·
          refine ⟨7881696620996453122942927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10508928827995270830590569 7881696620996453122942927)
          ·
            refine ⟨11822544931494679684414391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7881696620996453122942927 11822544931494679684414391)
            ·
              refine ⟨17733817397242019526621587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11822544931494679684414391 17733817397242019526621587)
              ·
                refine ⟨26600726095863029289932381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17733817397242019526621587 26600726095863029289932381)
                ·
                  refine ⟨9975272285948635983724643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26600726095863029289932381 9975272285948635983724643)
                  ·
                    refine ⟨14962908428922953975586965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9975272285948635983724643 14962908428922953975586965)
                    ·
                      refine ⟨701386332605763467605639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14962908428922953975586965 701386332605763467605639)
                      ·
                        rfl

theorem cell23_1365945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1365945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365945 prefixEnd_1365945 := by exact prefixLift 1365945
  have htrace : WordTrace (prefixWord ++ tailWord_1365945) baseStart_1365945 baseEnd_1365945 := by
    simpa [prefixWord, tailWord_1365945, baseEnd_1365945] using wordTrace_append hprefix tailTrace_1365945
  have hstable : (prefixWord ++ tailWord_1365945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365945).length < 2 ^ (prefixWord ++ tailWord_1365945).sum := by decide
  have hdescent : baseEnd_1365945 < baseStart_1365945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365952 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_1365952 : Nat := 118140960795 + 1365952 * 2 ^ 59
def prefixEnd_1365952 : Nat := 4983230072969 + 3 ^ 40 * 1365952 * 2
def baseEnd_1365952 : Nat := 701389926970344940218107

theorem tailTrace_1365952 : CollatzResearch.WordTrace tailWord_1365952 prefixEnd_1365952 701389926970344940218107 := by
  unfold tailWord_1365952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24910181173698332436930055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33213574898264443249240073 24910181173698332436930055)
  ·
    refine ⟨37365271760547498655395083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24910181173698332436930055 37365271760547498655395083)
    ·
      refine ⟨56047907640821247983092625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37365271760547498655395083 56047907640821247983092625)
      ·
        refine ⟨42035930730615935987319469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56047907640821247983092625 42035930730615935987319469)
        ·
          refine ⟨15763474023980975995244801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42035930730615935987319469 15763474023980975995244801)
          ·
            refine ⟨11822605517985731996433601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15763474023980975995244801 11822605517985731996433601)
            ·
              refine ⟨8866954138489298997325201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11822605517985731996433601 8866954138489298997325201)
              ·
                refine ⟨6650215603866974247993901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8866954138489298997325201 6650215603866974247993901)
                ·
                  refine ⟨2493830851450115342997713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6650215603866974247993901 2493830851450115342997713)
                  ·
                    refine ⟨1870373138587586507248285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2493830851450115342997713 1870373138587586507248285)
                    ·
                      refine ⟨701389926970344940218107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1870373138587586507248285 701389926970344940218107)
                      ·
                        rfl

theorem cell23_1365952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_1365952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365952 prefixEnd_1365952 := by exact prefixLift 1365952
  have htrace : WordTrace (prefixWord ++ tailWord_1365952) baseStart_1365952 baseEnd_1365952 := by
    simpa [prefixWord, tailWord_1365952, baseEnd_1365952] using wordTrace_append hprefix tailTrace_1365952
  have hstable : (prefixWord ++ tailWord_1365952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365952).length < 2 ^ (prefixWord ++ tailWord_1365952).sum := by decide
  have hdescent : baseEnd_1365952 < baseStart_1365952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365980 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1365980 : Nat := 118140960795 + 1365980 * 2 ^ 59
def prefixEnd_1365980 : Nat := 4983230072969 + 3 ^ 40 * 1365980 * 2
def baseEnd_1365980 : Nat := 233801434809556943555993

theorem tailTrace_1365980 : CollatzResearch.WordTrace tailWord_1365980 prefixEnd_1365980 233801434809556943555993 := by
  unfold tailWord_1365980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24910691795647612827939697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33214255727530150437252929 24910691795647612827939697)
  ·
    refine ⟨18683018846735709620954773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24910691795647612827939697 18683018846735709620954773)
    ·
      refine ⟨875766508440736388482255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18683018846735709620954773 875766508440736388482255)
      ·
        refine ⟨1313649762661104582723383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875766508440736388482255 1313649762661104582723383)
        ·
          refine ⟨1970474643991656874085075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313649762661104582723383 1970474643991656874085075)
          ·
            refine ⟨2955711965987485311127613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970474643991656874085075 2955711965987485311127613)
            ·
              refine ⟨1108391987245306991672855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2955711965987485311127613 1108391987245306991672855)
              ·
                refine ⟨1662587980867960487509283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108391987245306991672855 1662587980867960487509283)
                ·
                  refine ⟨2493881971301940731263925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1662587980867960487509283 2493881971301940731263925)
                  ·
                    refine ⟨233801434809556943555993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2493881971301940731263925 233801434809556943555993)
                    ·
                      rfl

theorem cell23_1365980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1365980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365980 prefixEnd_1365980 := by exact prefixLift 1365980
  have htrace : WordTrace (prefixWord ++ tailWord_1365980) baseStart_1365980 baseEnd_1365980 := by
    simpa [prefixWord, tailWord_1365980, baseEnd_1365980] using wordTrace_append hprefix tailTrace_1365980
  have hstable : (prefixWord ++ tailWord_1365980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365980).length < 2 ^ (prefixWord ++ tailWord_1365980).sum := by decide
  have hdescent : baseEnd_1365980 < baseStart_1365980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1365995 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5]
def baseStart_1365995 : Nat := 118140960795 + 1365995 * 2 ^ 59
def prefixEnd_1365995 : Nat := 4983230072969 + 3 ^ 40 * 1365995 * 2
def baseEnd_1365995 : Nat := 701412006638488271980409

theorem tailTrace_1365995 : CollatzResearch.WordTrace tailWord_1365995 prefixEnd_1365995 701412006638488271980409 := by
  unfold tailWord_1365995
  simp only [CollatzResearch.WordTrace]
  refine ⟨49821930686240883217675439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33214620457493922145116959 49821930686240883217675439)
  ·
    refine ⟨74732896029361324826513159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49821930686240883217675439 74732896029361324826513159)
    ·
      refine ⟨112099344044041987239769739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74732896029361324826513159 112099344044041987239769739)
      ·
        refine ⟨168149016066062980859654609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112099344044041987239769739 168149016066062980859654609)
        ·
          refine ⟨126111762049547235644740957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168149016066062980859654609 126111762049547235644740957)
          ·
            refine ⟨47291910768580213366777859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126111762049547235644740957 47291910768580213366777859)
            ·
              refine ⟨70937866152870320050166789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47291910768580213366777859 70937866152870320050166789)
              ·
                refine ⟨13300849903663185009406273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70937866152870320050166789 13300849903663185009406273)
                ·
                  refine ⟨9975637427747388757054705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13300849903663185009406273 9975637427747388757054705)
                  ·
                    refine ⟨7481728070810541567791029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9975637427747388757054705 7481728070810541567791029)
                    ·
                      refine ⟨701412006638488271980409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7481728070810541567791029 701412006638488271980409)
                      ·
                        rfl

theorem cell23_1365995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 5].length) (baseStart_1365995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1365995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1365995 prefixEnd_1365995 := by exact prefixLift 1365995
  have htrace : WordTrace (prefixWord ++ tailWord_1365995) baseStart_1365995 baseEnd_1365995 := by
    simpa [prefixWord, tailWord_1365995, baseEnd_1365995] using wordTrace_append hprefix tailTrace_1365995
  have hstable : (prefixWord ++ tailWord_1365995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1365995).length < 2 ^ (prefixWord ++ tailWord_1365995).sum := by decide
  have hdescent : baseEnd_1365995 < baseStart_1365995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1365995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366006 : List Nat := [5, 1, 1, 1, 5, 1, 1, 8]
def baseStart_1366006 : Nat := 118140960795 + 1366006 * 2 ^ 59
def prefixEnd_1366006 : Nat := 4983230072969 + 3 ^ 40 * 1366006 * 2
def baseEnd_1366006 : Nat := 25978431663914360331217

theorem tailTrace_1366006 : CollatzResearch.WordTrace tailWord_1366006 prefixEnd_1366006 25978431663914360331217 := by
  unfold tailWord_1366006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113895743075064506020367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33214887926134021397550581 3113895743075064506020367)
  ·
    refine ⟨4670843614612596759030551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113895743075064506020367 4670843614612596759030551)
    ·
      refine ⟨7006265421918895138545827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670843614612596759030551 7006265421918895138545827)
      ·
        refine ⟨10509398132878342707818741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7006265421918895138545827 10509398132878342707818741)
        ·
          refine ⟨985256074957344628858007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10509398132878342707818741 985256074957344628858007)
          ·
            refine ⟨1477884112436016943287011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985256074957344628858007 1477884112436016943287011)
            ·
              refine ⟨2216826168654025414930517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477884112436016943287011 2216826168654025414930517)
              ·
                refine ⟨25978431663914360331217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2216826168654025414930517 25978431663914360331217)
                ·
                  rfl

theorem cell23_1366006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_1366006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366006 prefixEnd_1366006 := by exact prefixLift 1366006
  have htrace : WordTrace (prefixWord ++ tailWord_1366006) baseStart_1366006 baseEnd_1366006 := by
    simpa [prefixWord, tailWord_1366006, baseEnd_1366006] using wordTrace_append hprefix tailTrace_1366006
  have hstable : (prefixWord ++ tailWord_1366006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366006).length < 2 ^ (prefixWord ++ tailWord_1366006).sum := by decide
  have hdescent : baseEnd_1366006 < baseStart_1366006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366009 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 3, 3, 2]
def baseStart_1366009 : Nat := 118140960795 + 1366009 * 2 ^ 59
def prefixEnd_1366009 : Nat := 4983230072969 + 3 ^ 40 * 1366009 * 2
def baseEnd_1366009 : Nat := 701419195367651217205345

theorem tailTrace_1366009 : CollatzResearch.WordTrace tailWord_1366009 prefixEnd_1366009 701419195367651217205345 := by
  unfold tailWord_1366009
  simp only [CollatzResearch.WordTrace]
  refine ⟨49822441308190163608685081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33214960872126775739123387 49822441308190163608685081)
  ·
    refine ⟨37366830981142622706513811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49822441308190163608685081 37366830981142622706513811)
    ·
      refine ⟨56050246471713934059770717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37366830981142622706513811 56050246471713934059770717)
      ·
        refine ⟨21018842426892725272414019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56050246471713934059770717 21018842426892725272414019)
        ·
          refine ⟨31528263640339087908621029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21018842426892725272414019 31528263640339087908621029)
          ·
            refine ⟨5911549432563578982866443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31528263640339087908621029 5911549432563578982866443)
            ·
              refine ⟨8867324148845368474299665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911549432563578982866443 8867324148845368474299665)
              ·
                refine ⟨6650493111634026355724749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8867324148845368474299665 6650493111634026355724749)
                ·
                  refine ⟨2493934916862759883396781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6650493111634026355724749 2493934916862759883396781)
                  ·
                    refine ⟨935225593823534956273793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2493934916862759883396781 935225593823534956273793)
                    ·
                      refine ⟨701419195367651217205345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935225593823534956273793 701419195367651217205345)
                      ·
                        rfl

theorem cell23_1366009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_1366009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366009 prefixEnd_1366009 := by exact prefixLift 1366009
  have htrace : WordTrace (prefixWord ++ tailWord_1366009) baseStart_1366009 baseEnd_1366009 := by
    simpa [prefixWord, tailWord_1366009, baseEnd_1366009] using wordTrace_append hprefix tailTrace_1366009
  have hstable : (prefixWord ++ tailWord_1366009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366009).length < 2 ^ (prefixWord ++ tailWord_1366009).sum := by decide
  have hdescent : baseEnd_1366009 < baseStart_1366009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366073 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1366073 : Nat := 118140960795 + 1366073 * 2 ^ 59
def prefixEnd_1366073 : Nat := 4983230072969 + 3 ^ 40 * 1366073 * 2
def baseEnd_1366073 : Nat := 701452058129538966805051

theorem tailTrace_1366073 : CollatzResearch.WordTrace tailWord_1366073 prefixEnd_1366073 701452058129538966805051 := by
  unfold tailWord_1366073
  simp only [CollatzResearch.WordTrace]
  refine ⟨49824775579958302539014873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33216517053305535026009915 49824775579958302539014873)
  ·
    refine ⟨37368581684968726904261155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49824775579958302539014873 37368581684968726904261155)
    ·
      refine ⟨56052872527453090356391733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37368581684968726904261155 56052872527453090356391733)
      ·
        refine ⟨5254956799448727220911725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56052872527453090356391733 5254956799448727220911725)
        ·
          refine ⟨1970608799793272707841897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5254956799448727220911725 1970608799793272707841897)
          ·
            refine ⟨1477956599844954530881423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970608799793272707841897 1477956599844954530881423)
            ·
              refine ⟨2216934899767431796322135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1477956599844954530881423 2216934899767431796322135)
              ·
                refine ⟨3325402349651147694483203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2216934899767431796322135 3325402349651147694483203)
                ·
                  refine ⟨4988103524476721541724805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3325402349651147694483203 4988103524476721541724805)
                  ·
                    refine ⟨935269410839385289073401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4988103524476721541724805 935269410839385289073401)
                    ·
                      refine ⟨701452058129538966805051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935269410839385289073401 701452058129538966805051)
                      ·
                        rfl

theorem cell23_1366073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1366073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366073 prefixEnd_1366073 := by exact prefixLift 1366073
  have htrace : WordTrace (prefixWord ++ tailWord_1366073) baseStart_1366073 baseEnd_1366073 := by
    simpa [prefixWord, tailWord_1366073, baseEnd_1366073] using wordTrace_append hprefix tailTrace_1366073
  have hstable : (prefixWord ++ tailWord_1366073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366073).length < 2 ^ (prefixWord ++ tailWord_1366073).sum := by decide
  have hdescent : baseEnd_1366073 < baseStart_1366073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366092 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_1366092 : Nat := 118140960795 + 1366092 * 2 ^ 59
def prefixEnd_1366092 : Nat := 4983230072969 + 3 ^ 40 * 1366092 * 2
def baseEnd_1366092 : Nat := 233820604753991464155821

theorem tailTrace_1366092 : CollatzResearch.WordTrace tailWord_1366092 prefixEnd_1366092 233820604753991464155821 := by
  unfold tailWord_1366092
  simp only [CollatzResearch.WordTrace]
  refine ⟨24912734283444734391978265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33216979044592979189304353 24912734283444734391978265)
  ·
    refine ⟨18684550712583550793983699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24912734283444734391978265 18684550712583550793983699)
    ·
      refine ⟨28026826068875326190975549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18684550712583550793983699 28026826068875326190975549)
      ·
        refine ⟨10510059775828247321615831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28026826068875326190975549 10510059775828247321615831)
        ·
          refine ⟨15765089663742370982423747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510059775828247321615831 15765089663742370982423747)
          ·
            refine ⟨23647634495613556473635621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15765089663742370982423747 23647634495613556473635621)
            ·
              refine ⟨4433931467927541838806679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23647634495613556473635621 4433931467927541838806679)
              ·
                refine ⟨6650897201891312758210019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4433931467927541838806679 6650897201891312758210019)
                ·
                  refine ⟨9976345802836969137315029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6650897201891312758210019 9976345802836969137315029)
                  ·
                    refine ⟨233820604753991464155821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9976345802836969137315029 233820604753991464155821)
                    ·
                      rfl

theorem cell23_1366092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_1366092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366092 prefixEnd_1366092 := by exact prefixLift 1366092
  have htrace : WordTrace (prefixWord ++ tailWord_1366092) baseStart_1366092 baseEnd_1366092 := by
    simpa [prefixWord, tailWord_1366092, baseEnd_1366092] using wordTrace_append hprefix tailTrace_1366092
  have hstable : (prefixWord ++ tailWord_1366092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366092).length < 2 ^ (prefixWord ++ tailWord_1366092).sum := by decide
  have hdescent : baseEnd_1366092 < baseStart_1366092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366129 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_1366129 : Nat := 118140960795 + 1366129 * 2 ^ 59
def prefixEnd_1366129 : Nat := 4983230072969 + 3 ^ 40 * 1366129 * 2
def baseEnd_1366129 : Nat := 701480813046190747704793

theorem tailTrace_1366129 : CollatzResearch.WordTrace tailWord_1366129 prefixEnd_1366129 701480813046190747704793 := by
  unfold tailWord_1366129
  simp only [CollatzResearch.WordTrace]
  refine ⟨49826818067755424103053441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33217878711836949402035627 49826818067755424103053441)
  ·
    refine ⟨37370113550816568077290081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49826818067755424103053441 37370113550816568077290081)
    ·
      refine ⟨28027585163112426057967561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37370113550816568077290081 28027585163112426057967561)
      ·
        refine ⟨21020688872334319543475671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28027585163112426057967561 21020688872334319543475671)
        ·
          refine ⟨31531033308501479315213507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21020688872334319543475671 31531033308501479315213507)
          ·
            refine ⟨47296549962752218972820261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31531033308501479315213507 47296549962752218972820261)
            ·
              refine ⟨8868103118016041057403799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47296549962752218972820261 8868103118016041057403799)
              ·
                refine ⟨13302154677024061586105699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8868103118016041057403799 13302154677024061586105699)
                ·
                  refine ⟨19953232015536092379158549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13302154677024061586105699 19953232015536092379158549)
                  ·
                    refine ⟨935307750728254330273057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19953232015536092379158549 935307750728254330273057)
                    ·
                      refine ⟨701480813046190747704793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935307750728254330273057 701480813046190747704793)
                      ·
                        rfl

theorem cell23_1366129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_1366129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366129 prefixEnd_1366129 := by exact prefixLift 1366129
  have htrace : WordTrace (prefixWord ++ tailWord_1366129) baseStart_1366129 baseEnd_1366129 := by
    simpa [prefixWord, tailWord_1366129, baseEnd_1366129] using wordTrace_append hprefix tailTrace_1366129
  have hstable : (prefixWord ++ tailWord_1366129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366129).length < 2 ^ (prefixWord ++ tailWord_1366129).sum := by decide
  have hdescent : baseEnd_1366129 < baseStart_1366129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366173 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1366173 : Nat := 118140960795 + 1366173 * 2 ^ 59
def prefixEnd_1366173 : Nat := 4983230072969 + 3 ^ 40 * 1366173 * 2
def baseEnd_1366173 : Nat := 233834468731662858518197

theorem tailTrace_1366173 : CollatzResearch.WordTrace tailWord_1366173 prefixEnd_1366173 233834468731662858518197 := by
  unfold tailWord_1366173
  simp only [CollatzResearch.WordTrace]
  refine ⟨49828422879596019617655173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33218948586397346411770115 49828422879596019617655173)
  ·
    refine ⟨9342829289924253678310345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49828422879596019617655173 9342829289924253678310345)
    ·
      refine ⟨7007121967443190258732759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9342829289924253678310345 7007121967443190258732759)
      ·
        refine ⟨10510682951164785388099139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7007121967443190258732759 10510682951164785388099139)
        ·
          refine ⟨15766024426747178082148709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10510682951164785388099139 15766024426747178082148709)
          ·
            refine ⟨2956129580015095890402883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15766024426747178082148709 2956129580015095890402883)
            ·
              refine ⟨4434194370022643835604325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956129580015095890402883 4434194370022643835604325)
              ·
                refine ⟨831411444379245719175811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4434194370022643835604325 831411444379245719175811)
                ·
                  refine ⟨1247117166568868578763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831411444379245719175811 1247117166568868578763717)
                  ·
                    refine ⟨233834468731662858518197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247117166568868578763717 233834468731662858518197)
                    ·
                      rfl

theorem cell23_1366173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1366173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366173 prefixEnd_1366173 := by exact prefixLift 1366173
  have htrace : WordTrace (prefixWord ++ tailWord_1366173) baseStart_1366173 baseEnd_1366173 := by
    simpa [prefixWord, tailWord_1366173, baseEnd_1366173] using wordTrace_append hprefix tailTrace_1366173
  have hstable : (prefixWord ++ tailWord_1366173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366173).length < 2 ^ (prefixWord ++ tailWord_1366173).sum := by decide
  have hdescent : baseEnd_1366173 < baseStart_1366173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366190 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1366190 : Nat := 118140960795 + 1366190 * 2 ^ 59
def prefixEnd_1366190 : Nat := 4983230072969 + 3 ^ 40 * 1366190 * 2
def baseEnd_1366190 : Nat := 233837378455371669680671

theorem tailTrace_1366190 : CollatzResearch.WordTrace tailWord_1366190 prefixEnd_1366190 233837378455371669680671 := by
  unfold tailWord_1366190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228630365066803940128003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33219361947022954347349349 6228630365066803940128003)
  ·
    refine ⟨9342945547600205910192005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6228630365066803940128003 9342945547600205910192005)
    ·
      refine ⟨1751802290175038608161001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9342945547600205910192005 1751802290175038608161001)
      ·
        refine ⟨1313851717631278956120751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1751802290175038608161001 1313851717631278956120751)
        ·
          refine ⟨1970777576446918434181127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313851717631278956120751 1970777576446918434181127)
          ·
            refine ⟨2956166364670377651271691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970777576446918434181127 2956166364670377651271691)
            ·
              refine ⟨4434249547005566476907537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2956166364670377651271691 4434249547005566476907537)
              ·
                refine ⟨3325687160254174857680653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4434249547005566476907537 3325687160254174857680653)
                ·
                  refine ⟨1247132685095315571630245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3325687160254174857680653 1247132685095315571630245)
                  ·
                    refine ⟨233837378455371669680671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247132685095315571630245 233837378455371669680671)
                    ·
                      rfl

theorem cell23_1366190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1366190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366190 prefixEnd_1366190 := by exact prefixLift 1366190
  have htrace : WordTrace (prefixWord ++ tailWord_1366190) baseStart_1366190 baseEnd_1366190 := by
    simpa [prefixWord, tailWord_1366190, baseEnd_1366190] using wordTrace_append hprefix tailTrace_1366190
  have hstable : (prefixWord ++ tailWord_1366190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366190).length < 2 ^ (prefixWord ++ tailWord_1366190).sum := by decide
  have hdescent : baseEnd_1366190 < baseStart_1366190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366199 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 3, 5]
def baseStart_1366199 : Nat := 118140960795 + 1366199 * 2 ^ 59
def prefixEnd_1366199 : Nat := 4983230072969 + 3 ^ 40 * 1366199 * 2
def baseEnd_1366199 : Nat := 233838918897335157943157

theorem tailTrace_1366199 : CollatzResearch.WordTrace tailWord_1366199 prefixEnd_1366199 233838918897335157943157 := by
  unfold tailWord_1366199
  simp only [CollatzResearch.WordTrace]
  refine ⟨49829371177501826058101651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33219580785001217372067767 49829371177501826058101651)
  ·
    refine ⟨74744056766252739087152477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49829371177501826058101651 74744056766252739087152477)
    ·
      refine ⟨28029021287344777157682179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74744056766252739087152477 28029021287344777157682179)
      ·
        refine ⟨42043531931017165736523269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28029021287344777157682179 42043531931017165736523269)
        ·
          refine ⟨7883162237065718575598113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42043531931017165736523269 7883162237065718575598113)
          ·
            refine ⟨5912371677799288931698585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7883162237065718575598113 5912371677799288931698585)
            ·
              refine ⟨4434278758349466698773939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5912371677799288931698585 4434278758349466698773939)
              ·
                refine ⟨6651418137524200048160909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4434278758349466698773939 6651418137524200048160909)
                ·
                  refine ⟨2494281801571575018060341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6651418137524200048160909 2494281801571575018060341)
                  ·
                    refine ⟨233838918897335157943157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2494281801571575018060341 233838918897335157943157)
                    ·
                      rfl

theorem cell23_1366199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_1366199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366199 prefixEnd_1366199 := by exact prefixLift 1366199
  have htrace : WordTrace (prefixWord ++ tailWord_1366199) baseStart_1366199 baseEnd_1366199 := by
    simpa [prefixWord, tailWord_1366199, baseEnd_1366199] using wordTrace_append hprefix tailTrace_1366199
  have hstable : (prefixWord ++ tailWord_1366199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366199).length < 2 ^ (prefixWord ++ tailWord_1366199).sum := by decide
  have hdescent : baseEnd_1366199 < baseStart_1366199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366213 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 3]
def baseStart_1366213 : Nat := 118140960795 + 1366213 * 2 ^ 59
def prefixEnd_1366213 : Nat := 4983230072969 + 3 ^ 40 * 1366213 * 2
def baseEnd_1366213 : Nat := 701523945421168419054407

theorem tailTrace_1366213 : CollatzResearch.WordTrace tailWord_1366213 prefixEnd_1366213 701523945421168419054407 := by
  unfold tailWord_1366213
  simp only [CollatzResearch.WordTrace]
  refine ⟨49829881799451106449111293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33219921199634070966074195 49829881799451106449111293)
  ·
    refine ⟨18686205674794164918416735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49829881799451106449111293 18686205674794164918416735)
    ·
      refine ⟨28029308512191247377625103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18686205674794164918416735 28029308512191247377625103)
      ·
        refine ⟨42043962768286871066437655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28029308512191247377625103 42043962768286871066437655)
        ·
          refine ⟨63065944152430306599656483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42043962768286871066437655 63065944152430306599656483)
          ·
            refine ⟨94598916228645459899484725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63065944152430306599656483 94598916228645459899484725)
            ·
              refine ⟨8868648396435511865576693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94598916228645459899484725 8868648396435511865576693)
              ·
                refine ⟨831435787165829237397815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8868648396435511865576693 831435787165829237397815)
                ·
                  refine ⟨1247153680748743856096723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831435787165829237397815 1247153680748743856096723)
                  ·
                    refine ⟨1870730521123115784145085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1247153680748743856096723 1870730521123115784145085)
                    ·
                      refine ⟨701523945421168419054407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1870730521123115784145085 701523945421168419054407)
                      ·
                        rfl

theorem cell23_1366213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_1366213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366213 prefixEnd_1366213 := by exact prefixLift 1366213
  have htrace : WordTrace (prefixWord ++ tailWord_1366213) baseStart_1366213 baseEnd_1366213 := by
    simpa [prefixWord, tailWord_1366213, baseEnd_1366213] using wordTrace_append hprefix tailTrace_1366213
  have hstable : (prefixWord ++ tailWord_1366213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366213).length < 2 ^ (prefixWord ++ tailWord_1366213).sum := by decide
  have hdescent : baseEnd_1366213 < baseStart_1366213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366220 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 6]
def baseStart_1366220 : Nat := 118140960795 + 1366220 * 2 ^ 59
def prefixEnd_1366220 : Nat := 4983230072969 + 3 ^ 40 * 1366220 * 2
def baseEnd_1366220 : Nat := 77947504420638876851875

theorem tailTrace_1366220 : CollatzResearch.WordTrace tailWord_1366220 prefixEnd_1366220 77947504420638876851875 := by
  unfold tailWord_1366220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24915068555212873322308057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33220091406950497763077409 24915068555212873322308057)
  ·
    refine ⟨18686301416409654991731043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24915068555212873322308057 18686301416409654991731043)
    ·
      refine ⟨28029452124614482487596565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18686301416409654991731043 28029452124614482487596565)
      ·
        refine ⟨1313880568341303866606089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28029452124614482487596565 1313880568341303866606089)
        ·
          refine ⟨985410426255977899954567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313880568341303866606089 985410426255977899954567)
          ·
            refine ⟨1478115639383966849931851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985410426255977899954567 1478115639383966849931851)
            ·
              refine ⟨2217173459075950274897777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478115639383966849931851 2217173459075950274897777)
              ·
                refine ⟨1662880094306962706173333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217173459075950274897777 1662880094306962706173333)
                ·
                  refine ⟨77947504420638876851875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1662880094306962706173333 77947504420638876851875)
                  ·
                    rfl

theorem cell23_1366220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_1366220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366220 prefixEnd_1366220 := by exact prefixLift 1366220
  have htrace : WordTrace (prefixWord ++ tailWord_1366220) baseStart_1366220 baseEnd_1366220 := by
    simpa [prefixWord, tailWord_1366220, baseEnd_1366220] using wordTrace_append hprefix tailTrace_1366220
  have hstable : (prefixWord ++ tailWord_1366220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366220).length < 2 ^ (prefixWord ++ tailWord_1366220).sum := by decide
  have hdescent : baseEnd_1366220 < baseStart_1366220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366230 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1366230 : Nat := 118140960795 + 1366230 * 2 ^ 59
def prefixEnd_1366230 : Nat := 4983230072969 + 3 ^ 40 * 1366230 * 2
def baseEnd_1366230 : Nat := 701532674592294852541829

theorem tailTrace_1366230 : CollatzResearch.WordTrace tailWord_1366230 prefixEnd_1366230 701532674592294852541829 := by
  unfold tailWord_1366230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114406365024344897030009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33220334560259678901653429 3114406365024344897030009)
  ·
    refine ⟨2335804773768258672772507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3114406365024344897030009 2335804773768258672772507)
    ·
      refine ⟨3503707160652388009158761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335804773768258672772507 3503707160652388009158761)
      ·
        refine ⟨2627780370489291006869071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3503707160652388009158761 2627780370489291006869071)
        ·
          refine ⟨3941670555733936510303607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627780370489291006869071 3941670555733936510303607)
          ·
            refine ⟨5912505833600904765455411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941670555733936510303607 5912505833600904765455411)
            ·
              refine ⟨8868758750401357148183117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912505833600904765455411 8868758750401357148183117)
              ·
                refine ⟨3325784531400508930568669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8868758750401357148183117 3325784531400508930568669)
                ·
                  refine ⟨1247169199275190848963251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3325784531400508930568669 1247169199275190848963251)
                  ·
                    refine ⟨1870753798912786273444877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1247169199275190848963251 1870753798912786273444877)
                    ·
                      refine ⟨701532674592294852541829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1870753798912786273444877 701532674592294852541829)
                      ·
                        rfl

theorem cell23_1366230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1366230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366230 prefixEnd_1366230 := by exact prefixLift 1366230
  have htrace : WordTrace (prefixWord ++ tailWord_1366230) baseStart_1366230 baseEnd_1366230 := by
    simpa [prefixWord, tailWord_1366230, baseEnd_1366230] using wordTrace_append hprefix tailTrace_1366230
  have hstable : (prefixWord ++ tailWord_1366230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366230).length < 2 ^ (prefixWord ++ tailWord_1366230).sum := by decide
  have hdescent : baseEnd_1366230 < baseStart_1366230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366276 : List Nat := [2, 3, 2, 2, 3, 2, 9]
def baseStart_1366276 : Nat := 118140960795 + 1366276 * 2 ^ 59
def prefixEnd_1366276 : Nat := 4983230072969 + 3 ^ 40 * 1366276 * 2
def baseEnd_1366276 : Nat := 8661188823486440402057

theorem tailTrace_1366276 : CollatzResearch.WordTrace tailWord_1366276 prefixEnd_1366276 8661188823486440402057 := by
  unfold tailWord_1366276
  simp only [CollatzResearch.WordTrace]
  refine ⟨24916089799111434104327341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33221453065481912139103121 24916089799111434104327341)
  ·
    refine ⟨9343533674666787789122753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24916089799111434104327341 9343533674666787789122753)
    ·
      refine ⟨7007650256000090841842065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9343533674666787789122753 7007650256000090841842065)
      ·
        refine ⟨5255737692000068131381549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7007650256000090841842065 5255737692000068131381549)
        ·
          refine ⟨1970901634500025549268081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5255737692000068131381549 1970901634500025549268081)
          ·
            refine ⟨1478176225875019161951061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970901634500025549268081 1478176225875019161951061)
            ·
              refine ⟨8661188823486440402057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1478176225875019161951061 8661188823486440402057)
              ·
                rfl

theorem cell23_1366276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 9].length) (baseStart_1366276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366276 prefixEnd_1366276 := by exact prefixLift 1366276
  have htrace : WordTrace (prefixWord ++ tailWord_1366276) baseStart_1366276 baseEnd_1366276 := by
    simpa [prefixWord, tailWord_1366276, baseEnd_1366276] using wordTrace_append hprefix tailTrace_1366276
  have hstable : (prefixWord ++ tailWord_1366276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366276).length < 2 ^ (prefixWord ++ tailWord_1366276).sum := by decide
  have hdescent : baseEnd_1366276 < baseStart_1366276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366337 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1366337 : Nat := 118140960795 + 1366337 * 2 ^ 59
def prefixEnd_1366337 : Nat := 4983230072969 + 3 ^ 40 * 1366337 * 2
def baseEnd_1366337 : Nat := 701587617022325933903837

theorem tailTrace_1366337 : CollatzResearch.WordTrace tailWord_1366337 prefixEnd_1366337 701587617022325933903837 := by
  unfold tailWord_1366337
  simp only [CollatzResearch.WordTrace]
  refine ⟨49834404451001875626625265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33222936300667917084416843 49834404451001875626625265)
  ·
    refine ⟨37375803338251406719968949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49834404451001875626625265 37375803338251406719968949)
    ·
      refine ⟨3503981562961069379997089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37375803338251406719968949 3503981562961069379997089)
      ·
        refine ⟨2627986172220802034997817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3503981562961069379997089 2627986172220802034997817)
        ·
          refine ⟨1970989629165601526248363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627986172220802034997817 1970989629165601526248363)
          ·
            refine ⟨2956484443748402289372545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970989629165601526248363 2956484443748402289372545)
            ·
              refine ⟨2217363332811301717029409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956484443748402289372545 2217363332811301717029409)
              ·
                refine ⟨1663022499608476287772057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2217363332811301717029409 1663022499608476287772057)
                ·
                  refine ⟨1247266874706357215829043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1663022499608476287772057 1247266874706357215829043)
                  ·
                    refine ⟨1870900312059535823743565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1247266874706357215829043 1870900312059535823743565)
                    ·
                      refine ⟨701587617022325933903837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1870900312059535823743565 701587617022325933903837)
                      ·
                        rfl

theorem cell23_1366337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1366337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366337 prefixEnd_1366337 := by exact prefixLift 1366337
  have htrace : WordTrace (prefixWord ++ tailWord_1366337) baseStart_1366337 baseEnd_1366337 := by
    simpa [prefixWord, tailWord_1366337, baseEnd_1366337] using wordTrace_append hprefix tailTrace_1366337
  have hstable : (prefixWord ++ tailWord_1366337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366337).length < 2 ^ (prefixWord ++ tailWord_1366337).sum := by decide
  have hdescent : baseEnd_1366337 < baseStart_1366337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366356 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1366356 : Nat := 118140960795 + 1366356 * 2 ^ 59
def prefixEnd_1366356 : Nat := 4983230072969 + 3 ^ 40 * 1366356 * 2
def baseEnd_1366356 : Nat := 701597373154761359566249

theorem tailTrace_1366356 : CollatzResearch.WordTrace tailWord_1366356 prefixEnd_1366356 701597373154761359566249 := by
  unfold tailWord_1366356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24917548718966520935783461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33223398291955361247711281 24917548718966520935783461)
  ·
    refine ⟨4672040384806222675459399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24917548718966520935783461 4672040384806222675459399)
    ·
      refine ⟨7008060577209334013189099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4672040384806222675459399 7008060577209334013189099)
      ·
        refine ⟨10512090865814001019783649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7008060577209334013189099 10512090865814001019783649)
        ·
          refine ⟨7884068149360500764837737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10512090865814001019783649 7884068149360500764837737)
          ·
            refine ⟨5913051112020375573628303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884068149360500764837737 5913051112020375573628303)
            ·
              refine ⟨8869576668030563360442455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913051112020375573628303 8869576668030563360442455)
              ·
                refine ⟨13304365002045845040663683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8869576668030563360442455 13304365002045845040663683)
                ·
                  refine ⟨19956547503068767560995525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13304365002045845040663683 19956547503068767560995525)
                  ·
                    refine ⟨3741852656825393917686661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19956547503068767560995525 3741852656825393917686661)
                    ·
                      refine ⟨701597373154761359566249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3741852656825393917686661 701597373154761359566249)
                      ·
                        rfl

theorem cell23_1366356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1366356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366356 prefixEnd_1366356 := by exact prefixLift 1366356
  have htrace : WordTrace (prefixWord ++ tailWord_1366356) baseStart_1366356 baseEnd_1366356 := by
    simpa [prefixWord, tailWord_1366356, baseEnd_1366356] using wordTrace_append hprefix tailTrace_1366356
  have hstable : (prefixWord ++ tailWord_1366356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366356).length < 2 ^ (prefixWord ++ tailWord_1366356).sum := by decide
  have hdescent : baseEnd_1366356 < baseStart_1366356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366379 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 7]
def baseStart_1366379 : Nat := 118140960795 + 1366379 * 2 ^ 59
def prefixEnd_1366379 : Nat := 4983230072969 + 3 ^ 40 * 1366379 * 2
def baseEnd_1366379 : Nat := 233869727736604923192881

theorem tailTrace_1366379 : CollatzResearch.WordTrace tailWord_1366379 prefixEnd_1366379 233869727736604923192881 := by
  unfold tailWord_1366379
  simp only [CollatzResearch.WordTrace]
  refine ⟨49835936316849716799654191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33223957544566477866436127 49835936316849716799654191)
  ·
    refine ⟨74753904475274575199481287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49835936316849716799654191 74753904475274575199481287)
    ·
      refine ⟨112130856712911862799221931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74753904475274575199481287 112130856712911862799221931)
      ·
        refine ⟨168196285069367794198832897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112130856712911862799221931 168196285069367794198832897)
        ·
          refine ⟨126147213802025845649124673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168196285069367794198832897 126147213802025845649124673)
          ·
            refine ⟨94610410351519384236843505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126147213802025845649124673 94610410351519384236843505)
            ·
              refine ⟨70957807763639538177632629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94610410351519384236843505 70957807763639538177632629)
              ·
                refine ⟨6652294477841206704153059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70957807763639538177632629 6652294477841206704153059)
                ·
                  refine ⟨9978441716761810056229589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6652294477841206704153059 9978441716761810056229589)
                  ·
                    refine ⟨233869727736604923192881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9978441716761810056229589 233869727736604923192881)
                    ·
                      rfl

theorem cell23_1366379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_1366379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366379 prefixEnd_1366379 := by exact prefixLift 1366379
  have htrace : WordTrace (prefixWord ++ tailWord_1366379) baseStart_1366379 baseEnd_1366379 := by
    simpa [prefixWord, tailWord_1366379, baseEnd_1366379] using wordTrace_append hprefix tailTrace_1366379
  have hstable : (prefixWord ++ tailWord_1366379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366379).length < 2 ^ (prefixWord ++ tailWord_1366379).sum := by decide
  have hdescent : baseEnd_1366379 < baseStart_1366379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366456 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 6]
def baseStart_1366456 : Nat := 118140960795 + 1366456 * 2 ^ 59
def prefixEnd_1366456 : Nat := 4983230072969 + 3 ^ 40 * 1366456 * 2
def baseEnd_1366456 : Nat := 77960969024467885368421

theorem tailTrace_1366456 : CollatzResearch.WordTrace tailWord_1366456 prefixEnd_1366456 77960969024467885368421 := by
  unfold tailWord_1366456
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919372368785379475103611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33225829825047172633471481 24919372368785379475103611)
  ·
    refine ⟨37379058553178069212655417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24919372368785379475103611 37379058553178069212655417)
    ·
      refine ⟨28034293914883551909491563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37379058553178069212655417 28034293914883551909491563)
      ·
        refine ⟨42051440872325327864237345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28034293914883551909491563 42051440872325327864237345)
        ·
          refine ⟨31538580654243995898178009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42051440872325327864237345 31538580654243995898178009)
          ·
            refine ⟨23653935490682996923633507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31538580654243995898178009 23653935490682996923633507)
            ·
              refine ⟨35480903236024495385450261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23653935490682996923633507 35480903236024495385450261)
              ·
                refine ⟨1663167339188648221192981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35480903236024495385450261 1663167339188648221192981)
                ·
                  refine ⟨77960969024467885368421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1663167339188648221192981 77960969024467885368421)
                  ·
                    rfl

theorem cell23_1366456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_1366456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366456 prefixEnd_1366456 := by exact prefixLift 1366456
  have htrace : WordTrace (prefixWord ++ tailWord_1366456) baseStart_1366456 baseEnd_1366456 := by
    simpa [prefixWord, tailWord_1366456, baseEnd_1366456] using wordTrace_append hprefix tailTrace_1366456
  have hstable : (prefixWord ++ tailWord_1366456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366456).length < 2 ^ (prefixWord ++ tailWord_1366456).sum := by decide
  have hdescent : baseEnd_1366456 < baseStart_1366456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366460 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1366460 : Nat := 118140960795 + 1366460 * 2 ^ 59
def prefixEnd_1366460 : Nat := 4983230072969 + 3 ^ 40 * 1366460 * 2
def baseEnd_1366460 : Nat := 233883591714276317555257

theorem tailTrace_1366460 : CollatzResearch.WordTrace tailWord_1366460 prefixEnd_1366460 233883591714276317555257 := by
  unfold tailWord_1366460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24919445314778133816676417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33225927086370845088901889 24919445314778133816676417)
  ·
    refine ⟨18689583986083600362507313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24919445314778133816676417 18689583986083600362507313)
    ·
      refine ⟨14017187989562700271880485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18689583986083600362507313 14017187989562700271880485)
      ·
        refine ⟨2628222748043006300977591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14017187989562700271880485 2628222748043006300977591)
        ·
          refine ⟨3942334122064509451466387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628222748043006300977591 3942334122064509451466387)
          ·
            refine ⟨5913501183096764177199581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3942334122064509451466387 5913501183096764177199581)
            ·
              refine ⟨2217562943661286566449843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5913501183096764177199581 2217562943661286566449843)
              ·
                refine ⟨3326344415491929849674765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217562943661286566449843 3326344415491929849674765)
                ·
                  refine ⟨1247379155809473693628037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3326344415491929849674765 1247379155809473693628037)
                  ·
                    refine ⟨233883591714276317555257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1247379155809473693628037 233883591714276317555257)
                    ·
                      rfl

theorem cell23_1366460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1366460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366460 prefixEnd_1366460 := by exact prefixLift 1366460
  have htrace : WordTrace (prefixWord ++ tailWord_1366460) baseStart_1366460 baseEnd_1366460 := by
    simpa [prefixWord, tailWord_1366460, baseEnd_1366460] using wordTrace_append hprefix tailTrace_1366460
  have hstable : (prefixWord ++ tailWord_1366460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366460).length < 2 ^ (prefixWord ++ tailWord_1366460).sum := by decide
  have hdescent : baseEnd_1366460 < baseStart_1366460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366473 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 6]
def baseStart_1366473 : Nat := 118140960795 + 1366473 * 2 ^ 59
def prefixEnd_1366473 : Nat := 4983230072969 + 3 ^ 40 * 1366473 * 2
def baseEnd_1366473 : Nat := 77961938932370822422579

theorem tailTrace_1366473 : CollatzResearch.WordTrace tailWord_1366473 prefixEnd_1366473 77961938932370822422579 := by
  unfold tailWord_1366473
  simp only [CollatzResearch.WordTrace]
  refine ⟨49839364778509170853576073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33226243185672780569050715 49839364778509170853576073)
  ·
    refine ⟨37379523583881878140182055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49839364778509170853576073 37379523583881878140182055)
    ·
      refine ⟨56069285375822817210273083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37379523583881878140182055 56069285375822817210273083)
      ·
        refine ⟨84103928063734225815409625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56069285375822817210273083 84103928063734225815409625)
        ·
          refine ⟨63077946047800669361557219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84103928063734225815409625 63077946047800669361557219)
          ·
            refine ⟨94616919071701004042335829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63077946047800669361557219 94616919071701004042335829)
            ·
              refine ⟨1108792020371496141121123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 94616919071701004042335829 1108792020371496141121123)
              ·
                refine ⟨1663188030557244211681685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108792020371496141121123 1663188030557244211681685)
                ·
                  refine ⟨77961938932370822422579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1663188030557244211681685 77961938932370822422579)
                  ·
                    rfl

theorem cell23_1366473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 6].length) (baseStart_1366473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366473 prefixEnd_1366473 := by exact prefixLift 1366473
  have htrace : WordTrace (prefixWord ++ tailWord_1366473) baseStart_1366473 baseEnd_1366473 := by
    simpa [prefixWord, tailWord_1366473, baseEnd_1366473] using wordTrace_append hprefix tailTrace_1366473
  have hstable : (prefixWord ++ tailWord_1366473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366473).length < 2 ^ (prefixWord ++ tailWord_1366473).sum := by decide
  have hdescent : baseEnd_1366473 < baseStart_1366473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366551 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1366551 : Nat := 118140960795 + 1366551 * 2 ^ 59
def prefixEnd_1366551 : Nat := 4983230072969 + 3 ^ 40 * 1366551 * 2
def baseEnd_1366551 : Nat := 701697501882388096627853

theorem tailTrace_1366551 : CollatzResearch.WordTrace tailWord_1366551 prefixEnd_1366551 701697501882388096627853 := by
  unfold tailWord_1366551
  simp only [CollatzResearch.WordTrace]
  refine ⟨49842209672226590174915507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33228139781484393449943671 49842209672226590174915507)
  ·
    refine ⟨74763314508339885262373261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49842209672226590174915507 74763314508339885262373261)
    ·
      refine ⟨28036242940627456973389973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74763314508339885262373261 28036242940627456973389973)
      ·
        refine ⟨1314198887841912045627655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28036242940627456973389973 1314198887841912045627655)
        ·
          refine ⟨1971298331762868068441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314198887841912045627655 1971298331762868068441483)
          ·
            refine ⟨2956947497644302102662225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971298331762868068441483 2956947497644302102662225)
            ·
              refine ⟨2217710623233226576996669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2956947497644302102662225 2217710623233226576996669)
              ·
                refine ⟨831641483712459966373751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2217710623233226576996669 831641483712459966373751)
                ·
                  refine ⟨1247462225568689949560627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831641483712459966373751 1247462225568689949560627)
                  ·
                    refine ⟨1871193338353034924340941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1247462225568689949560627 1871193338353034924340941)
                    ·
                      refine ⟨701697501882388096627853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1871193338353034924340941 701697501882388096627853)
                      ·
                        rfl

theorem cell23_1366551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1366551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366551 prefixEnd_1366551 := by exact prefixLift 1366551
  have htrace : WordTrace (prefixWord ++ tailWord_1366551) baseStart_1366551 baseEnd_1366551 := by
    simpa [prefixWord, tailWord_1366551, baseEnd_1366551] using wordTrace_append hprefix tailTrace_1366551
  have hstable : (prefixWord ++ tailWord_1366551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366551).length < 2 ^ (prefixWord ++ tailWord_1366551).sum := by decide
  have hdescent : baseEnd_1366551 < baseStart_1366551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366557 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_1366557 : Nat := 118140960795 + 1366557 * 2 ^ 59
def prefixEnd_1366557 : Nat := 4983230072969 + 3 ^ 40 * 1366557 * 2
def baseEnd_1366557 : Nat := 701700582766315073152825

theorem tailTrace_1366557 : CollatzResearch.WordTrace tailWord_1366557 prefixEnd_1366557 701700582766315073152825 := by
  unfold tailWord_1366557
  simp only [CollatzResearch.WordTrace]
  refine ⟨49842428510204853199633925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33228285673469902133089283 49842428510204853199633925)
  ·
    refine ⟨9345455345663409974931361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49842428510204853199633925 9345455345663409974931361)
    ·
      refine ⟨7009091509247557481198521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9345455345663409974931361 7009091509247557481198521)
      ·
        refine ⟨5256818631935668110898891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7009091509247557481198521 5256818631935668110898891)
        ·
          refine ⟨7885227947903502166348337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5256818631935668110898891 7885227947903502166348337)
          ·
            refine ⟨5913920960927626624761253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7885227947903502166348337 5913920960927626624761253)
            ·
              refine ⟨1108860180173929992142735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5913920960927626624761253 1108860180173929992142735)
              ·
                refine ⟨1663290270260894988214103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108860180173929992142735 1663290270260894988214103)
                ·
                  refine ⟨2494935405391342482321155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663290270260894988214103 2494935405391342482321155)
                  ·
                    refine ⟨3742403108087013723481733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2494935405391342482321155 3742403108087013723481733)
                    ·
                      refine ⟨701700582766315073152825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3742403108087013723481733 701700582766315073152825)
                      ·
                        rfl

theorem cell23_1366557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_1366557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366557 prefixEnd_1366557 := by exact prefixLift 1366557
  have htrace : WordTrace (prefixWord ++ tailWord_1366557) baseStart_1366557 baseEnd_1366557 := by
    simpa [prefixWord, tailWord_1366557, baseEnd_1366557] using wordTrace_append hprefix tailTrace_1366557
  have hstable : (prefixWord ++ tailWord_1366557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366557).length < 2 ^ (prefixWord ++ tailWord_1366557).sum := by decide
  have hdescent : baseEnd_1366557 < baseStart_1366557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366576 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_1366576 : Nat := 118140960795 + 1366576 * 2 ^ 59
def prefixEnd_1366576 : Nat := 4983230072969 + 3 ^ 40 * 1366576 * 2
def baseEnd_1366576 : Nat := 233903446299583499605079

theorem tailTrace_1366576 : CollatzResearch.WordTrace tailWord_1366576 prefixEnd_1366576 233903446299583499605079 := by
  unfold tailWord_1366576
  simp only [CollatzResearch.WordTrace]
  refine ⟨24921560748568009722287791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33228747664757346296383721 24921560748568009722287791)
  ·
    refine ⟨37382341122852014583431687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24921560748568009722287791 37382341122852014583431687)
    ·
      refine ⟨56073511684278021875147531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37382341122852014583431687 56073511684278021875147531)
      ·
        refine ⟨84110267526417032812721297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56073511684278021875147531 84110267526417032812721297)
        ·
          refine ⟨63082700644812774609540973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84110267526417032812721297 63082700644812774609540973)
          ·
            refine ⟨23656012741804790478577865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63082700644812774609540973 23656012741804790478577865)
            ·
              refine ⟨17742009556353592858933399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23656012741804790478577865 17742009556353592858933399)
              ·
                refine ⟨26613014334530389288400099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17742009556353592858933399 26613014334530389288400099)
                ·
                  refine ⟨39919521501795583932600149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26613014334530389288400099 39919521501795583932600149)
                  ·
                    refine ⟨233903446299583499605079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39919521501795583932600149 233903446299583499605079)
                    ·
                      rfl

theorem cell23_1366576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_1366576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366576 prefixEnd_1366576 := by exact prefixLift 1366576
  have htrace : WordTrace (prefixWord ++ tailWord_1366576) baseStart_1366576 baseEnd_1366576 := by
    simpa [prefixWord, tailWord_1366576, baseEnd_1366576] using wordTrace_append hprefix tailTrace_1366576
  have hstable : (prefixWord ++ tailWord_1366576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366576).length < 2 ^ (prefixWord ++ tailWord_1366576).sum := by decide
  have hdescent : baseEnd_1366576 < baseStart_1366576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366600 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_1366600 : Nat := 118140960795 + 1366600 * 2 ^ 59
def prefixEnd_1366600 : Nat := 4983230072969 + 3 ^ 40 * 1366600 * 2
def baseEnd_1366600 : Nat := 701722662434458404915127

theorem tailTrace_1366600 : CollatzResearch.WordTrace tailWord_1366600 prefixEnd_1366600 701722662434458404915127 := by
  unfold tailWord_1366600
  simp only [CollatzResearch.WordTrace]
  refine ⟨24921998424524535771724627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33229331232699381028966169 24921998424524535771724627)
  ·
    refine ⟨37382997636786803657586941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24921998424524535771724627 37382997636786803657586941)
    ·
      refine ⟨14018624113795051371595103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37382997636786803657586941 14018624113795051371595103)
      ·
        refine ⟨21027936170692577057392655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14018624113795051371595103 21027936170692577057392655)
        ·
          refine ⟨31541904256038865586088983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21027936170692577057392655 31541904256038865586088983)
          ·
            refine ⟨47312856384058298379133475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31541904256038865586088983 47312856384058298379133475)
            ·
              refine ⟨70969284576087447568700213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47312856384058298379133475 70969284576087447568700213)
              ·
                refine ⟨6653370429008198209565645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70969284576087447568700213 6653370429008198209565645)
                ·
                  refine ⟨2495013910878074328587117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6653370429008198209565645 2495013910878074328587117)
                  ·
                    refine ⟨935630216579277873220169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495013910878074328587117 935630216579277873220169)
                    ·
                      refine ⟨701722662434458404915127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935630216579277873220169 701722662434458404915127)
                      ·
                        rfl

theorem cell23_1366600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_1366600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366600 prefixEnd_1366600 := by exact prefixLift 1366600
  have htrace : WordTrace (prefixWord ++ tailWord_1366600) baseStart_1366600 baseEnd_1366600 := by
    simpa [prefixWord, tailWord_1366600, baseEnd_1366600] using wordTrace_append hprefix tailTrace_1366600
  have hstable : (prefixWord ++ tailWord_1366600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366600).length < 2 ^ (prefixWord ++ tailWord_1366600).sum := by decide
  have hdescent : baseEnd_1366600 < baseStart_1366600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366633 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_1366633 : Nat := 118140960795 + 1366633 * 2 ^ 59
def prefixEnd_1366633 : Nat := 4983230072969 + 3 ^ 40 * 1366633 * 2
def baseEnd_1366633 : Nat := 701739607296056775802475

theorem tailTrace_1366633 : CollatzResearch.WordTrace tailWord_1366633 prefixEnd_1366633 701739607296056775802475 := by
  unfold tailWord_1366633
  simp only [CollatzResearch.WordTrace]
  refine ⟨49845200457929518179400553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33230133638619678786267035 49845200457929518179400553)
  ·
    refine ⟨37383900343447138634550415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49845200457929518179400553 37383900343447138634550415)
    ·
      refine ⟨56075850515170707951825623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37383900343447138634550415 56075850515170707951825623)
      ·
        refine ⟨84113775772756061927738435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56075850515170707951825623 84113775772756061927738435)
        ·
          refine ⟨126170663659134092891607653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84113775772756061927738435 126170663659134092891607653)
          ·
            refine ⟨23656999436087642417176435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126170663659134092891607653 23656999436087642417176435)
            ·
              refine ⟨35485499154131463625764653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23656999436087642417176435 35485499154131463625764653)
              ·
                refine ⟨13307062182799298859661745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35485499154131463625764653 13307062182799298859661745)
                ·
                  refine ⟨9980296637099474144746309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13307062182799298859661745 9980296637099474144746309)
                  ·
                    refine ⟨1871305619456151402139933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9980296637099474144746309 1871305619456151402139933)
                    ·
                      refine ⟨701739607296056775802475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1871305619456151402139933 701739607296056775802475)
                      ·
                        rfl

theorem cell23_1366633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_1366633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366633 prefixEnd_1366633 := by exact prefixLift 1366633
  have htrace : WordTrace (prefixWord ++ tailWord_1366633) baseStart_1366633 baseEnd_1366633 := by
    simpa [prefixWord, tailWord_1366633, baseEnd_1366633] using wordTrace_append hprefix tailTrace_1366633
  have hstable : (prefixWord ++ tailWord_1366633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366633).length < 2 ^ (prefixWord ++ tailWord_1366633).sum := by decide
  have hdescent : baseEnd_1366633 < baseStart_1366633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366680 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_1366680 : Nat := 118140960795 + 1366680 * 2 ^ 59
def prefixEnd_1366680 : Nat := 4983230072969 + 3 ^ 40 * 1366680 * 2
def baseEnd_1366680 : Nat := 701763740886818091914759

theorem tailTrace_1366680 : CollatzResearch.WordTrace tailWord_1366680 prefixEnd_1366680 701763740886818091914759 := by
  unfold tailWord_1366680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24923457344379622603180747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33231276459172830137574329 24923457344379622603180747)
  ·
    refine ⟨37385186016569433904771121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24923457344379622603180747 37385186016569433904771121)
    ·
      refine ⟨28038889512427075428578341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37385186016569433904771121 28038889512427075428578341)
      ·
        refine ⟨5257291783580076642858439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28038889512427075428578341 5257291783580076642858439)
        ·
          refine ⟨7885937675370114964287659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257291783580076642858439 7885937675370114964287659)
          ·
            refine ⟨11828906513055172446431489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7885937675370114964287659 11828906513055172446431489)
            ·
              refine ⟨8871679884791379334823617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11828906513055172446431489 8871679884791379334823617)
              ·
                refine ⟨6653759913593534501117713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8871679884791379334823617 6653759913593534501117713)
                ·
                  refine ⟨4990319935195150875838285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6653759913593534501117713 4990319935195150875838285)
                  ·
                    refine ⟨1871369975698181578439357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4990319935195150875838285 1871369975698181578439357)
                    ·
                      refine ⟨701763740886818091914759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1871369975698181578439357 701763740886818091914759)
                      ·
                        rfl

theorem cell23_1366680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_1366680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366680 prefixEnd_1366680 := by exact prefixLift 1366680
  have htrace : WordTrace (prefixWord ++ tailWord_1366680) baseStart_1366680 baseEnd_1366680 := by
    simpa [prefixWord, tailWord_1366680, baseEnd_1366680] using wordTrace_append hprefix tailTrace_1366680
  have hstable : (prefixWord ++ tailWord_1366680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366680).length < 2 ^ (prefixWord ++ tailWord_1366680).sum := by decide
  have hdescent : baseEnd_1366680 < baseStart_1366680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366717 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1366717 : Nat := 118140960795 + 1366717 * 2 ^ 59
def prefixEnd_1366717 : Nat := 4983230072969 + 3 ^ 40 * 1366717 * 2
def baseEnd_1366717 : Nat := 233927579890344815717363

theorem tailTrace_1366717 : CollatzResearch.WordTrace tailWord_1366717 prefixEnd_1366717 233927579890344815717363 := by
  unfold tailWord_1366717
  simp only [CollatzResearch.WordTrace]
  refine ⟨49848264189625200525458405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33232176126416800350305603 49848264189625200525458405)
  ·
    refine ⟨9346549535554725098523451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49848264189625200525458405 9346549535554725098523451)
    ·
      refine ⟨14019824303332087647785177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9346549535554725098523451 14019824303332087647785177)
      ·
        refine ⟨10514868227499065735838883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14019824303332087647785177 10514868227499065735838883)
        ·
          refine ⟨15772302341248598603758325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10514868227499065735838883 15772302341248598603758325)
          ·
            refine ⟨1478653344492056119102343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15772302341248598603758325 1478653344492056119102343)
            ·
              refine ⟨2217980016738084178653515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478653344492056119102343 2217980016738084178653515)
              ·
                refine ⟨3326970025107126267980273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217980016738084178653515 3326970025107126267980273)
                ·
                  refine ⟨2495227518830344700985205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3326970025107126267980273 2495227518830344700985205)
                  ·
                    refine ⟨233927579890344815717363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2495227518830344700985205 233927579890344815717363)
                    ·
                      rfl

theorem cell23_1366717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1366717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366717 prefixEnd_1366717 := by exact prefixLift 1366717
  have htrace : WordTrace (prefixWord ++ tailWord_1366717) baseStart_1366717 baseEnd_1366717 := by
    simpa [prefixWord, tailWord_1366717, baseEnd_1366717] using wordTrace_append hprefix tailTrace_1366717
  have hstable : (prefixWord ++ tailWord_1366717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366717).length < 2 ^ (prefixWord ++ tailWord_1366717).sum := by decide
  have hdescent : baseEnd_1366717 < baseStart_1366717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366720 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_1366720 : Nat := 118140960795 + 1366720 * 2 ^ 59
def prefixEnd_1366720 : Nat := 4983230072969 + 3 ^ 40 * 1366720 * 2
def baseEnd_1366720 : Nat := 701784280112997935414575

theorem tailTrace_1366720 : CollatzResearch.WordTrace tailWord_1366720 prefixEnd_1366720 701784280112997935414575 := by
  unfold tailWord_1366720
  simp only [CollatzResearch.WordTrace]
  refine ⟨24924186804307166018908807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33232249072409554691878409 24924186804307166018908807)
  ·
    refine ⟨37386280206460749028363211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24924186804307166018908807 37386280206460749028363211)
    ·
      refine ⟨56079420309691123542544817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37386280206460749028363211 56079420309691123542544817)
      ·
        refine ⟨42059565232268342656908613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56079420309691123542544817 42059565232268342656908613)
        ·
          refine ⟨7886168481050314248170365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42059565232268342656908613 7886168481050314248170365)
          ·
            refine ⟨2957313180393867843063887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7886168481050314248170365 2957313180393867843063887)
            ·
              refine ⟨4435969770590801764595831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2957313180393867843063887 4435969770590801764595831)
              ·
                refine ⟨6653954655886202646893747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4435969770590801764595831 6653954655886202646893747)
                ·
                  refine ⟨9980931983829303970340621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6653954655886202646893747 9980931983829303970340621)
                  ·
                    refine ⟨3742849493935988988877733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9980931983829303970340621 3742849493935988988877733)
                    ·
                      refine ⟨701784280112997935414575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3742849493935988988877733 701784280112997935414575)
                      ·
                        rfl

theorem cell23_1366720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_1366720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366720 prefixEnd_1366720 := by exact prefixLift 1366720
  have htrace : WordTrace (prefixWord ++ tailWord_1366720) baseStart_1366720 baseEnd_1366720 := by
    simpa [prefixWord, tailWord_1366720, baseEnd_1366720] using wordTrace_append hprefix tailTrace_1366720
  have hstable : (prefixWord ++ tailWord_1366720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366720).length < 2 ^ (prefixWord ++ tailWord_1366720).sum := by decide
  have hdescent : baseEnd_1366720 < baseStart_1366720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366721 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 5]
def baseStart_1366721 : Nat := 118140960795 + 1366721 * 2 ^ 59
def prefixEnd_1366721 : Nat := 4983230072969 + 3 ^ 40 * 1366721 * 2
def baseEnd_1366721 : Nat := 77976088177072492389119

theorem tailTrace_1366721 : CollatzResearch.WordTrace tailWord_1366721 prefixEnd_1366721 77976088177072492389119 := by
  unfold tailWord_1366721
  simp only [CollatzResearch.WordTrace]
  refine ⟨49848410081610709208604017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33232273387740472805736011 49848410081610709208604017)
  ·
    refine ⟨37386307561208031906453013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49848410081610709208604017 37386307561208031906453013)
    ·
      refine ⟨1752483166931626495614985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37386307561208031906453013 1752483166931626495614985)
      ·
        refine ⟨1314362375198719871711239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1752483166931626495614985 1314362375198719871711239)
        ·
          refine ⟨1971543562798079807566859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314362375198719871711239 1971543562798079807566859)
          ·
            refine ⟨2957315344197119711350289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971543562798079807566859 2957315344197119711350289)
            ·
              refine ⟨2217986508147839783512717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957315344197119711350289 2217986508147839783512717)
              ·
                refine ⟨831744940555439918817269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2217986508147839783512717 831744940555439918817269)
                ·
                  refine ⟨77976088177072492389119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 831744940555439918817269 77976088177072492389119)
                  ·
                    rfl

theorem cell23_1366721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 5].length) (baseStart_1366721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366721 prefixEnd_1366721 := by exact prefixLift 1366721
  have htrace : WordTrace (prefixWord ++ tailWord_1366721) baseStart_1366721 baseEnd_1366721 := by
    simpa [prefixWord, tailWord_1366721, baseEnd_1366721] using wordTrace_append hprefix tailTrace_1366721
  have hstable : (prefixWord ++ tailWord_1366721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366721).length < 2 ^ (prefixWord ++ tailWord_1366721).sum := by decide
  have hdescent : baseEnd_1366721 < baseStart_1366721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366763 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6]
def baseStart_1366763 : Nat := 118140960795 + 1366763 * 2 ^ 59
def prefixEnd_1366763 : Nat := 4983230072969 + 3 ^ 40 * 1366763 * 2
def baseEnd_1366763 : Nat := 701806359781141267176877

theorem tailTrace_1366763 : CollatzResearch.WordTrace tailWord_1366763 prefixEnd_1366763 701806359781141267176877 := by
  unfold tailWord_1366763
  simp only [CollatzResearch.WordTrace]
  refine ⟨49849941947458550381632943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33233294631639033587755295 49849941947458550381632943)
  ·
    refine ⟨74774912921187825572449415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49849941947458550381632943 74774912921187825572449415)
    ·
      refine ⟨112162369381781738358674123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74774912921187825572449415 112162369381781738358674123)
      ·
        refine ⟨168243554072672607538011185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112162369381781738358674123 168243554072672607538011185)
        ·
          refine ⟨126182665554504455653508389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168243554072672607538011185 126182665554504455653508389)
          ·
            refine ⟨23659249791469585435032823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126182665554504455653508389 23659249791469585435032823)
            ·
              refine ⟨35488874687204378152549235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23659249791469585435032823 35488874687204378152549235)
              ·
                refine ⟨53233312030806567228823853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35488874687204378152549235 53233312030806567228823853)
                ·
                  refine ⟨19962492011552462710808945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53233312030806567228823853 19962492011552462710808945)
                  ·
                    refine ⟨14971869008664347033106709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19962492011552462710808945 14971869008664347033106709)
                    ·
                      refine ⟨701806359781141267176877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14971869008664347033106709 701806359781141267176877)
                      ·
                        rfl

theorem cell23_1366763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_1366763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366763 prefixEnd_1366763 := by exact prefixLift 1366763
  have htrace : WordTrace (prefixWord ++ tailWord_1366763) baseStart_1366763 baseEnd_1366763 := by
    simpa [prefixWord, tailWord_1366763, baseEnd_1366763] using wordTrace_append hprefix tailTrace_1366763
  have hstable : (prefixWord ++ tailWord_1366763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366763).length < 2 ^ (prefixWord ++ tailWord_1366763).sum := by decide
  have hdescent : baseEnd_1366763 < baseStart_1366763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366837 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1366837 : Nat := 118140960795 + 1366837 * 2 ^ 59
def prefixEnd_1366837 : Nat := 4983230072969 + 3 ^ 40 * 1366837 * 2
def baseEnd_1366837 : Nat := 233948119116524659217179

theorem tailTrace_1366837 : CollatzResearch.WordTrace tailWord_1366837 prefixEnd_1366837 233948119116524659217179 := by
  unfold tailWord_1366837
  simp only [CollatzResearch.WordTrace]
  refine ⟨49852640949190461019826765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33235093966126974013217843 49852640949190461019826765)
  ·
    refine ⟨18694740355946422882435037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49852640949190461019826765 18694740355946422882435037)
    ·
      refine ⟨7010527633479908580913139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18694740355946422882435037 7010527633479908580913139)
      ·
        refine ⟨10515791450219862871369709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010527633479908580913139 10515791450219862871369709)
        ·
          refine ⟨3943421793832448576763641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10515791450219862871369709 3943421793832448576763641)
          ·
            refine ⟨2957566345374336432572731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3943421793832448576763641 2957566345374336432572731)
            ·
              refine ⟨4436349518061504648859097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2957566345374336432572731 4436349518061504648859097)
              ·
                refine ⟨3327262138546128486644323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4436349518061504648859097 3327262138546128486644323)
                ·
                  refine ⟨4990893207819192729966485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327262138546128486644323 4990893207819192729966485)
                  ·
                    refine ⟨233948119116524659217179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4990893207819192729966485 233948119116524659217179)
                    ·
                      rfl

theorem cell23_1366837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1366837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366837 prefixEnd_1366837 := by exact prefixLift 1366837
  have htrace : WordTrace (prefixWord ++ tailWord_1366837) baseStart_1366837 baseEnd_1366837 := by
    simpa [prefixWord, tailWord_1366837, baseEnd_1366837] using wordTrace_append hprefix tailTrace_1366837
  have hstable : (prefixWord ++ tailWord_1366837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366837).length < 2 ^ (prefixWord ++ tailWord_1366837).sum := by decide
  have hdescent : baseEnd_1366837 < baseStart_1366837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366847 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_1366847 : Nat := 118140960795 + 1366847 * 2 ^ 59
def prefixEnd_1366847 : Nat := 4983230072969 + 3 ^ 40 * 1366847 * 2
def baseEnd_1366847 : Nat := 701849492156118938526491

theorem tailTrace_1366847 : CollatzResearch.WordTrace tailWord_1366847 prefixEnd_1366847 701849492156118938526491 := by
  unfold tailWord_1366847
  simp only [CollatzResearch.WordTrace]
  refine ⟨49853005679154232727690795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33235337119436155151793863 49853005679154232727690795)
  ·
    refine ⟨74779508518731349091536193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49853005679154232727690795 74779508518731349091536193)
    ·
      refine ⟨56084631389048511818652145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74779508518731349091536193 56084631389048511818652145)
      ·
        refine ⟨42063473541786383863989109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56084631389048511818652145 42063473541786383863989109)
        ·
          refine ⟨3943450644542473487248979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42063473541786383863989109 3943450644542473487248979)
          ·
            refine ⟨5915175966813710230873469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943450644542473487248979 5915175966813710230873469)
            ·
              refine ⟨2218190987555141336577551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5915175966813710230873469 2218190987555141336577551)
              ·
                refine ⟨3327286481332712004866327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218190987555141336577551 3327286481332712004866327)
                ·
                  refine ⟨4990929721999068007299491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327286481332712004866327 4990929721999068007299491)
                  ·
                    refine ⟨7486394582998602010949237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4990929721999068007299491 7486394582998602010949237)
                    ·
                      refine ⟨701849492156118938526491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7486394582998602010949237 701849492156118938526491)
                      ·
                        rfl

theorem cell23_1366847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_1366847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366847 prefixEnd_1366847 := by exact prefixLift 1366847
  have htrace : WordTrace (prefixWord ++ tailWord_1366847) baseStart_1366847 baseEnd_1366847 := by
    simpa [prefixWord, tailWord_1366847, baseEnd_1366847] using wordTrace_append hprefix tailTrace_1366847
  have hstable : (prefixWord ++ tailWord_1366847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366847).length < 2 ^ (prefixWord ++ tailWord_1366847).sum := by decide
  have hdescent : baseEnd_1366847 < baseStart_1366847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366880 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_1366880 : Nat := 118140960795 + 1366880 * 2 ^ 59
def prefixEnd_1366880 : Nat := 4983230072969 + 3 ^ 40 * 1366880 * 2
def baseEnd_1366880 : Nat := 233955479005905769804613

theorem tailTrace_1366880 : CollatzResearch.WordTrace tailWord_1366880 prefixEnd_1366880 233955479005905769804613 := by
  unfold tailWord_1366880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24927104644017339681821047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33236139525356452909094729 24927104644017339681821047)
  ·
    refine ⟨37390656966026009522731571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24927104644017339681821047 37390656966026009522731571)
    ·
      refine ⟨56085985449039014284097357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37390656966026009522731571 56085985449039014284097357)
      ·
        refine ⟨21032244543389630356536509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56085985449039014284097357 21032244543389630356536509)
        ·
          refine ⟨7887091703771111383701191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21032244543389630356536509 7887091703771111383701191)
          ·
            refine ⟨11830637555656667075551787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7887091703771111383701191 11830637555656667075551787)
            ·
              refine ⟨17745956333485000613327681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11830637555656667075551787 17745956333485000613327681)
              ·
                refine ⟨13309467250113750459995761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17745956333485000613327681 13309467250113750459995761)
                ·
                  refine ⟨9982100437585312844996821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13309467250113750459995761 9982100437585312844996821)
                  ·
                    refine ⟨233955479005905769804613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9982100437585312844996821 233955479005905769804613)
                    ·
                      rfl

theorem cell23_1366880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_1366880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366880 prefixEnd_1366880 := by exact prefixLift 1366880
  have htrace : WordTrace (prefixWord ++ tailWord_1366880) baseStart_1366880 baseEnd_1366880 := by
    simpa [prefixWord, tailWord_1366880, baseEnd_1366880] using wordTrace_append hprefix tailTrace_1366880
  have hstable : (prefixWord ++ tailWord_1366880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366880).length < 2 ^ (prefixWord ++ tailWord_1366880).sum := by decide
  have hdescent : baseEnd_1366880 < baseStart_1366880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366938 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1366938 : Nat := 118140960795 + 1366938 * 2 ^ 59
def prefixEnd_1366938 : Nat := 4983230072969 + 3 ^ 40 * 1366938 * 2
def baseEnd_1366938 : Nat := 701896218895678082488573

theorem tailTrace_1366938 : CollatzResearch.WordTrace tailWord_1366938 prefixEnd_1366938 701896218895678082488573 := by
  unfold tailWord_1366938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12464081180456138817313367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33237549814549703512835645 12464081180456138817313367)
  ·
    refine ⟨18696121770684208225970051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12464081180456138817313367 18696121770684208225970051)
    ·
      refine ⟨28044182656026312338955077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18696121770684208225970051 28044182656026312338955077)
      ·
        refine ⟨5258284248004933563554077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28044182656026312338955077 5258284248004933563554077)
        ·
          refine ⟨1971856593001850086332779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5258284248004933563554077 1971856593001850086332779)
          ·
            refine ⟨2957784889502775129499169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971856593001850086332779 2957784889502775129499169)
            ·
              refine ⟨2218338667127081347124377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957784889502775129499169 2218338667127081347124377)
              ·
                refine ⟨1663754000345311010343283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218338667127081347124377 1663754000345311010343283)
                ·
                  refine ⟨2495631000517966515514925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663754000345311010343283 2495631000517966515514925)
                  ·
                    refine ⟨935861625194237443318097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495631000517966515514925 935861625194237443318097)
                    ·
                      refine ⟨701896218895678082488573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935861625194237443318097 701896218895678082488573)
                      ·
                        rfl

theorem cell23_1366938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1366938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366938 prefixEnd_1366938 := by exact prefixLift 1366938
  have htrace : WordTrace (prefixWord ++ tailWord_1366938) baseStart_1366938 baseEnd_1366938 := by
    simpa [prefixWord, tailWord_1366938, baseEnd_1366938] using wordTrace_append hprefix tailTrace_1366938
  have hstable : (prefixWord ++ tailWord_1366938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366938).length < 2 ^ (prefixWord ++ tailWord_1366938).sum := by decide
  have hdescent : baseEnd_1366938 < baseStart_1366938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366960 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_1366960 : Nat := 118140960795 + 1366960 * 2 ^ 59
def prefixEnd_1366960 : Nat := 4983230072969 + 3 ^ 40 * 1366960 * 2
def baseEnd_1366960 : Nat := 701907515470076996413471

theorem tailTrace_1366960 : CollatzResearch.WordTrace tailWord_1366960 prefixEnd_1366960 701907515470076996413471 := by
  unfold tailWord_1366960
  simp only [CollatzResearch.WordTrace]
  refine ⟨24928563563872426513277167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33238084751829902017702889 24928563563872426513277167)
  ·
    refine ⟨37392845345808639769915751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24928563563872426513277167 37392845345808639769915751)
    ·
      refine ⟨56089268018712959654873627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37392845345808639769915751 56089268018712959654873627)
      ·
        refine ⟨84133902028069439482310441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56089268018712959654873627 84133902028069439482310441)
        ·
          refine ⟨63100426521052079611732831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84133902028069439482310441 63100426521052079611732831)
          ·
            refine ⟨94650639781578119417599247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63100426521052079611732831 94650639781578119417599247)
            ·
              refine ⟨141975959672367179126398871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94650639781578119417599247 141975959672367179126398871)
              ·
                refine ⟨212963939508550768689598307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141975959672367179126398871 212963939508550768689598307)
                ·
                  refine ⟨319445909262826153034397461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212963939508550768689598307 319445909262826153034397461)
                  ·
                    refine ⟨14974026996694975923487381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 319445909262826153034397461 14974026996694975923487381)
                    ·
                      refine ⟨701907515470076996413471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14974026996694975923487381 701907515470076996413471)
                      ·
                        rfl

theorem cell23_1366960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_1366960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366960 prefixEnd_1366960 := by exact prefixLift 1366960
  have htrace : WordTrace (prefixWord ++ tailWord_1366960) baseStart_1366960 baseEnd_1366960 := by
    simpa [prefixWord, tailWord_1366960, baseEnd_1366960] using wordTrace_append hprefix tailTrace_1366960
  have hstable : (prefixWord ++ tailWord_1366960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366960).length < 2 ^ (prefixWord ++ tailWord_1366960).sum := by decide
  have hdescent : baseEnd_1366960 < baseStart_1366960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366967 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_1366967 : Nat := 118140960795 + 1366967 * 2 ^ 59
def prefixEnd_1366967 : Nat := 4983230072969 + 3 ^ 40 * 1366967 * 2
def baseEnd_1366967 : Nat := 701911109834658469025939

theorem tailTrace_1366967 : CollatzResearch.WordTrace tailWord_1366967 prefixEnd_1366967 701911109834658469025939 := by
  unfold tailWord_1366967
  simp only [CollatzResearch.WordTrace]
  refine ⟨49857382438719493222059155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33238254959146328814706103 49857382438719493222059155)
  ·
    refine ⟨74786073658079239833088733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49857382438719493222059155 74786073658079239833088733)
    ·
      refine ⟨28044777621779714937408275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74786073658079239833088733 28044777621779714937408275)
      ·
        refine ⟨42067166432669572406112413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28044777621779714937408275 42067166432669572406112413)
        ·
          refine ⟨15775187412251089652292155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42067166432669572406112413 15775187412251089652292155)
          ·
            refine ⟨23662781118376634478438233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15775187412251089652292155 23662781118376634478438233)
            ·
              refine ⟨17747085838782475858828675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23662781118376634478438233 17747085838782475858828675)
              ·
                refine ⟨26620628758173713788243013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17747085838782475858828675 26620628758173713788243013)
                ·
                  refine ⟨4991367892157571335295565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26620628758173713788243013 4991367892157571335295565)
                  ·
                    refine ⟨1871762959559089250735837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4991367892157571335295565 1871762959559089250735837)
                    ·
                      refine ⟨701911109834658469025939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1871762959559089250735837 701911109834658469025939)
                      ·
                        rfl

theorem cell23_1366967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_1366967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366967 prefixEnd_1366967 := by exact prefixLift 1366967
  have htrace : WordTrace (prefixWord ++ tailWord_1366967) baseStart_1366967 baseEnd_1366967 := by
    simpa [prefixWord, tailWord_1366967, baseEnd_1366967] using wordTrace_append hprefix tailTrace_1366967
  have hstable : (prefixWord ++ tailWord_1366967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366967).length < 2 ^ (prefixWord ++ tailWord_1366967).sum := by decide
  have hdescent : baseEnd_1366967 < baseStart_1366967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1366989 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1366989 : Nat := 118140960795 + 1366989 * 2 ^ 59
def prefixEnd_1366989 : Nat := 4983230072969 + 3 ^ 40 * 1366989 * 2
def baseEnd_1366989 : Nat := 701922406409057382950839

theorem tailTrace_1366989 : CollatzResearch.WordTrace tailWord_1366989 prefixEnd_1366989 701922406409057382950839 := by
  unfold tailWord_1366989
  simp only [CollatzResearch.WordTrace]
  refine ⟨49858184844639790979360021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33238789896426527319573347 49858184844639790979360021)
  ·
    refine ⟨2337102414592490202157501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49858184844639790979360021 2337102414592490202157501)
    ·
      refine ⟨876413405472183825809063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2337102414592490202157501 876413405472183825809063)
      ·
        refine ⟨1314620108208275738713595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876413405472183825809063 1314620108208275738713595)
        ·
          refine ⟨1971930162312413608070393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314620108208275738713595 1971930162312413608070393)
          ·
            refine ⟨1478947621734310206052795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971930162312413608070393 1478947621734310206052795)
            ·
              refine ⟨2218421432601465309079193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478947621734310206052795 2218421432601465309079193)
              ·
                refine ⟨1663816074451098981809395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218421432601465309079193 1663816074451098981809395)
                ·
                  refine ⟨2495724111676648472714093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663816074451098981809395 2495724111676648472714093)
                  ·
                    refine ⟨935896541878743177267785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2495724111676648472714093 935896541878743177267785)
                    ·
                      refine ⟨701922406409057382950839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935896541878743177267785 701922406409057382950839)
                      ·
                        rfl

theorem cell23_1366989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1366989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1366989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1366989 prefixEnd_1366989 := by exact prefixLift 1366989
  have htrace : WordTrace (prefixWord ++ tailWord_1366989) baseStart_1366989 baseEnd_1366989 := by
    simpa [prefixWord, tailWord_1366989, baseEnd_1366989] using wordTrace_append hprefix tailTrace_1366989
  have hstable : (prefixWord ++ tailWord_1366989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1366989).length < 2 ^ (prefixWord ++ tailWord_1366989).sum := by decide
  have hdescent : baseEnd_1366989 < baseStart_1366989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1366989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367024 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2]
def baseStart_1367024 : Nat := 118140960795 + 1367024 * 2 ^ 59
def prefixEnd_1367024 : Nat := 4983230072969 + 3 ^ 40 * 1367024 * 2
def baseEnd_1367024 : Nat := 701940378231964746013177

theorem tailTrace_1367024 : CollatzResearch.WordTrace tailWord_1367024 prefixEnd_1367024 701940378231964746013177 := by
  unfold tailWord_1367024
  simp only [CollatzResearch.WordTrace]
  refine ⟨24929730699756495978442063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33239640933008661304589417 24929730699756495978442063)
  ·
    refine ⟨37394596049634743967663095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24929730699756495978442063 37394596049634743967663095)
    ·
      refine ⟨56091894074452115951494643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37394596049634743967663095 56091894074452115951494643)
      ·
        refine ⟨84137841111678173927241965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56091894074452115951494643 84137841111678173927241965)
        ·
          refine ⟨31551690416879315222715737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84137841111678173927241965 31551690416879315222715737)
          ·
            refine ⟨23663767812659486417036803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31551690416879315222715737 23663767812659486417036803)
            ·
              refine ⟨35495651718989229625555205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23663767812659486417036803 35495651718989229625555205)
              ·
                refine ⟨6655434697310480554791601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35495651718989229625555205 6655434697310480554791601)
                ·
                  refine ⟨4991576022982860416093701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6655434697310480554791601 4991576022982860416093701)
                  ·
                    refine ⟨935920504309286328017569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4991576022982860416093701 935920504309286328017569)
                    ·
                      refine ⟨701940378231964746013177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935920504309286328017569 701940378231964746013177)
                      ·
                        rfl

theorem cell23_1367024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 4, 2].length) (baseStart_1367024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367024 prefixEnd_1367024 := by exact prefixLift 1367024
  have htrace : WordTrace (prefixWord ++ tailWord_1367024) baseStart_1367024 baseEnd_1367024 := by
    simpa [prefixWord, tailWord_1367024, baseEnd_1367024] using wordTrace_append hprefix tailTrace_1367024
  have hstable : (prefixWord ++ tailWord_1367024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367024).length < 2 ^ (prefixWord ++ tailWord_1367024).sum := by decide
  have hdescent : baseEnd_1367024 < baseStart_1367024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367027 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3]
def baseStart_1367027 : Nat := 118140960795 + 1367027 * 2 ^ 59
def prefixEnd_1367027 : Nat := 4983230072969 + 3 ^ 40 * 1367027 * 2
def baseEnd_1367027 : Nat := 701941918673928234275663

theorem tailTrace_1367027 : CollatzResearch.WordTrace tailWord_1367027 prefixEnd_1367027 701941918673928234275663 := by
  unfold tailWord_1367027
  simp only [CollatzResearch.WordTrace]
  refine ⟨49859570818502123469243335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33239713879001415646162223 49859570818502123469243335)
  ·
    refine ⟨74789356227753185203865003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49859570818502123469243335 74789356227753185203865003)
    ·
      refine ⟨112184034341629777805797505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74789356227753185203865003 112184034341629777805797505)
      ·
        refine ⟨84138025756222333354348129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112184034341629777805797505 84138025756222333354348129)
        ·
          refine ⟨63103519317166750015761097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84138025756222333354348129 63103519317166750015761097)
          ·
            refine ⟨47327639487875062511820823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63103519317166750015761097 47327639487875062511820823)
            ·
              refine ⟨70991459231812593767731235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47327639487875062511820823 70991459231812593767731235)
              ·
                refine ⟨106487188847718890651596853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70991459231812593767731235 106487188847718890651596853)
                ·
                  refine ⟨9983173954473645998587205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106487188847718890651596853 9983173954473645998587205)
                  ·
                    refine ⟨1871845116463808624735101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9983173954473645998587205 1871845116463808624735101)
                    ·
                      refine ⟨701941918673928234275663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1871845116463808624735101 701941918673928234275663)
                      ·
                        rfl

theorem cell23_1367027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_1367027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367027 prefixEnd_1367027 := by exact prefixLift 1367027
  have htrace : WordTrace (prefixWord ++ tailWord_1367027) baseStart_1367027 baseEnd_1367027 := by
    simpa [prefixWord, tailWord_1367027, baseEnd_1367027] using wordTrace_append hprefix tailTrace_1367027
  have hstable : (prefixWord ++ tailWord_1367027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367027).length < 2 ^ (prefixWord ++ tailWord_1367027).sum := by decide
  have hdescent : baseEnd_1367027 < baseStart_1367027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367037 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1367037 : Nat := 118140960795 + 1367037 * 2 ^ 59
def prefixEnd_1367037 : Nat := 4983230072969 + 3 ^ 40 * 1367037 * 2
def baseEnd_1367037 : Nat := 701947053480473195150617

theorem tailTrace_1367037 : CollatzResearch.WordTrace tailWord_1367037 prefixEnd_1367037 701947053480473195150617 := by
  unfold tailWord_1367037
  simp only [CollatzResearch.WordTrace]
  refine ⟨49859935548465895177107365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33239957032310596784738243 49859935548465895177107365)
  ·
    refine ⟨9348737915337355345707631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49859935548465895177107365 9348737915337355345707631)
    ·
      refine ⟨14023106873006033018561447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9348737915337355345707631 14023106873006033018561447)
      ·
        refine ⟨21034660309509049527842171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023106873006033018561447 21034660309509049527842171)
        ·
          refine ⟨31551990464263574291763257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21034660309509049527842171 31551990464263574291763257)
          ·
            refine ⟨23663992848197680718822443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31551990464263574291763257 23663992848197680718822443)
            ·
              refine ⟨35495989272296521078233665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23663992848197680718822443 35495989272296521078233665)
              ·
                refine ⟨26621991954222390808675249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35495989272296521078233665 26621991954222390808675249)
                ·
                  refine ⟨19966493965666793106506437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26621991954222390808675249 19966493965666793106506437)
                  ·
                    refine ⟨3743717618562523707469957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19966493965666793106506437 3743717618562523707469957)
                    ·
                      refine ⟨701947053480473195150617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3743717618562523707469957 701947053480473195150617)
                      ·
                        rfl

theorem cell23_1367037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1367037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367037 prefixEnd_1367037 := by exact prefixLift 1367037
  have htrace : WordTrace (prefixWord ++ tailWord_1367037) baseStart_1367037 baseEnd_1367037 := by
    simpa [prefixWord, tailWord_1367037, baseEnd_1367037] using wordTrace_append hprefix tailTrace_1367037
  have hstable : (prefixWord ++ tailWord_1367037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367037).length < 2 ^ (prefixWord ++ tailWord_1367037).sum := by decide
  have hdescent : baseEnd_1367037 < baseStart_1367037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367041 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_1367041 : Nat := 118140960795 + 1367041 * 2 ^ 59
def prefixEnd_1367041 : Nat := 4983230072969 + 3 ^ 40 * 1367041 * 2
def baseEnd_1367041 : Nat := 701949107403091179500599

theorem tailTrace_1367041 : CollatzResearch.WordTrace tailWord_1367041 prefixEnd_1367041 701949107403091179500599 := by
  unfold tailWord_1367041
  simp only [CollatzResearch.WordTrace]
  refine ⟨49860081440451403860252977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33240054293634269240168651 49860081440451403860252977)
  ·
    refine ⟨37395061080338552895189733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49860081440451403860252977 37395061080338552895189733)
    ·
      refine ⟨7011573952563478667848075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37395061080338552895189733 7011573952563478667848075)
      ·
        refine ⟨10517360928845218001772113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011573952563478667848075 10517360928845218001772113)
        ·
          refine ⟨7888020696633913501329085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10517360928845218001772113 7888020696633913501329085)
          ·
            refine ⟨2958007761237717562998407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7888020696633913501329085 2958007761237717562998407)
            ·
              refine ⟨4437011641856576344497611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958007761237717562998407 4437011641856576344497611)
              ·
                refine ⟨6655517462784864516746417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437011641856576344497611 6655517462784864516746417)
                ·
                  refine ⟨4991638097088648387559813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6655517462784864516746417 4991638097088648387559813)
                  ·
                    refine ⟨935932143204121572667465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4991638097088648387559813 935932143204121572667465)
                    ·
                      refine ⟨701949107403091179500599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935932143204121572667465 701949107403091179500599)
                      ·
                        rfl

theorem cell23_1367041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_1367041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367041 prefixEnd_1367041 := by exact prefixLift 1367041
  have htrace : WordTrace (prefixWord ++ tailWord_1367041) baseStart_1367041 baseEnd_1367041 := by
    simpa [prefixWord, tailWord_1367041, baseEnd_1367041] using wordTrace_append hprefix tailTrace_1367041
  have hstable : (prefixWord ++ tailWord_1367041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367041).length < 2 ^ (prefixWord ++ tailWord_1367041).sum := by decide
  have hdescent : baseEnd_1367041 < baseStart_1367041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367061 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1367061 : Nat := 118140960795 + 1367061 * 2 ^ 59
def prefixEnd_1367061 : Nat := 4983230072969 + 3 ^ 40 * 1367061 * 2
def baseEnd_1367061 : Nat := 701959377016181101250507

theorem tailTrace_1367061 : CollatzResearch.WordTrace tailWord_1367061 prefixEnd_1367061 701959377016181101250507 := by
  unfold tailWord_1367061
  simp only [CollatzResearch.WordTrace]
  refine ⟨49860810900378947275981037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33240540600252631517320691 49860810900378947275981037)
  ·
    refine ⟨18697804087642105228492889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49860810900378947275981037 18697804087642105228492889)
    ·
      refine ⟨14023353065731578921369667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18697804087642105228492889 14023353065731578921369667)
      ·
        refine ⟨21035029598597368382054501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023353065731578921369667 21035029598597368382054501)
        ·
          refine ⟨3944068049737006571635219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21035029598597368382054501 3944068049737006571635219)
          ·
            refine ⟨5916102074605509857452829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944068049737006571635219 5916102074605509857452829)
            ·
              refine ⟨2218538277977066196544811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5916102074605509857452829 2218538277977066196544811)
              ·
                refine ⟨3327807416965599294817217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218538277977066196544811 3327807416965599294817217)
                ·
                  refine ⟨2495855562724199471112913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3327807416965599294817217 2495855562724199471112913)
                  ·
                    refine ⟨1871891672043149603334685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2495855562724199471112913 1871891672043149603334685)
                    ·
                      refine ⟨701959377016181101250507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1871891672043149603334685 701959377016181101250507)
                      ·
                        rfl

theorem cell23_1367061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1367061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367061 prefixEnd_1367061 := by exact prefixLift 1367061
  have htrace : WordTrace (prefixWord ++ tailWord_1367061) baseStart_1367061 baseEnd_1367061 := by
    simpa [prefixWord, tailWord_1367061, baseEnd_1367061] using wordTrace_append hprefix tailTrace_1367061
  have hstable : (prefixWord ++ tailWord_1367061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367061).length < 2 ^ (prefixWord ++ tailWord_1367061).sum := by decide
  have hdescent : baseEnd_1367061 < baseStart_1367061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367101 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_1367101 : Nat := 118140960795 + 1367101 * 2 ^ 59
def prefixEnd_1367101 : Nat := 4983230072969 + 3 ^ 40 * 1367101 * 2
def baseEnd_1367101 : Nat := 701979916242360944750323

theorem tailTrace_1367101 : CollatzResearch.WordTrace tailWord_1367101 prefixEnd_1367101 701979916242360944750323 := by
  unfold tailWord_1367101
  simp only [CollatzResearch.WordTrace]
  refine ⟨49862269820234034107437157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33241513213489356071624771 49862269820234034107437157)
  ·
    refine ⟨9349175591293881395144467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49862269820234034107437157 9349175591293881395144467)
    ·
      refine ⟨14023763386940822092716701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349175591293881395144467 14023763386940822092716701)
      ·
        refine ⟨5258911270102808284768763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14023763386940822092716701 5258911270102808284768763)
        ·
          refine ⟨7888366905154212427153145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258911270102808284768763 7888366905154212427153145)
          ·
            refine ⟨5916275178865659320364859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7888366905154212427153145 5916275178865659320364859)
            ·
              refine ⟨8874412768298488980547289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5916275178865659320364859 8874412768298488980547289)
              ·
                refine ⟨6655809576223866735410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8874412768298488980547289 6655809576223866735410467)
                ·
                  refine ⟨9983714364335800103115701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6655809576223866735410467 9983714364335800103115701)
                  ·
                    refine ⟨935973221656481259667097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9983714364335800103115701 935973221656481259667097)
                    ·
                      refine ⟨701979916242360944750323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 935973221656481259667097 701979916242360944750323)
                      ·
                        rfl

theorem cell23_1367101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_1367101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367101 prefixEnd_1367101 := by exact prefixLift 1367101
  have htrace : WordTrace (prefixWord ++ tailWord_1367101) baseStart_1367101 baseEnd_1367101 := by
    simpa [prefixWord, tailWord_1367101, baseEnd_1367101] using wordTrace_append hprefix tailTrace_1367101
  have hstable : (prefixWord ++ tailWord_1367101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367101).length < 2 ^ (prefixWord ++ tailWord_1367101).sum := by decide
  have hdescent : baseEnd_1367101 < baseStart_1367101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367111 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 1, 5]
def baseStart_1367111 : Nat := 118140960795 + 1367111 * 2 ^ 59
def prefixEnd_1367111 : Nat := 4983230072969 + 3 ^ 40 * 1367111 * 2
def baseEnd_1367111 : Nat := 233995017016301968541759

theorem tailTrace_1367111 : CollatzResearch.WordTrace tailWord_1367111 prefixEnd_1367111 233995017016301968541759 := by
  unfold tailWord_1367111
  simp only [CollatzResearch.WordTrace]
  refine ⟨49862634550197805815301187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33241756366798537210200791 49862634550197805815301187)
  ·
    refine ⟨74793951825296708722951781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49862634550197805815301187 74793951825296708722951781)
    ·
      refine ⟨14023865967243132885553459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74793951825296708722951781 14023865967243132885553459)
      ·
        refine ⟨21035798950864699328330189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023865967243132885553459 21035798950864699328330189)
        ·
          refine ⟨7888424606574262248123821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21035798950864699328330189 7888424606574262248123821)
          ·
            refine ⟨2958159227465348343046433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7888424606574262248123821 2958159227465348343046433)
            ·
              refine ⟨2218619420599011257284825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2958159227465348343046433 2218619420599011257284825)
              ·
                refine ⟨1663964565449258442963619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218619420599011257284825 1663964565449258442963619)
                ·
                  refine ⟨2495946848173887664445429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663964565449258442963619 2495946848173887664445429)
                  ·
                    refine ⟨233995017016301968541759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2495946848173887664445429 233995017016301968541759)
                    ·
                      rfl

theorem cell23_1367111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_1367111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367111 prefixEnd_1367111 := by exact prefixLift 1367111
  have htrace : WordTrace (prefixWord ++ tailWord_1367111) baseStart_1367111 baseEnd_1367111 := by
    simpa [prefixWord, tailWord_1367111, baseEnd_1367111] using wordTrace_append hprefix tailTrace_1367111
  have hstable : (prefixWord ++ tailWord_1367111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367111).length < 2 ^ (prefixWord ++ tailWord_1367111).sum := by decide
  have hdescent : baseEnd_1367111 < baseStart_1367111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367114 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1367114 : Nat := 118140960795 + 1367114 * 2 ^ 59
def prefixEnd_1367114 : Nat := 4983230072969 + 3 ^ 40 * 1367114 * 2
def baseEnd_1367114 : Nat := 701986591490869393887763

theorem tailTrace_1367114 : CollatzResearch.WordTrace tailWord_1367114 prefixEnd_1367114 701986591490869393887763 := by
  unfold tailWord_1367114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465685992296734331915099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33241829312791291551773597 12465685992296734331915099)
  ·
    refine ⟨18698528988445101497872649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12465685992296734331915099 18698528988445101497872649)
    ·
      refine ⟨14023896741333826123404487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18698528988445101497872649 14023896741333826123404487)
      ·
        refine ⟨21035845112000739185106731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14023896741333826123404487 21035845112000739185106731)
        ·
          refine ⟨31553767668001108777660097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21035845112000739185106731 31553767668001108777660097)
          ·
            refine ⟨23665325751000831583245073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31553767668001108777660097 23665325751000831583245073)
            ·
              refine ⟨17748994313250623687433805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23665325751000831583245073 17748994313250623687433805)
              ·
                refine ⟨6655872867468983882787677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17748994313250623687433805 6655872867468983882787677)
                ·
                  refine ⟨2495952325300868956045379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6655872867468983882787677 2495952325300868956045379)
                  ·
                    refine ⟨3743928487951303434068069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2495952325300868956045379 3743928487951303434068069)
                    ·
                      refine ⟨701986591490869393887763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3743928487951303434068069 701986591490869393887763)
                      ·
                        rfl

theorem cell23_1367114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1367114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367114 prefixEnd_1367114 := by exact prefixLift 1367114
  have htrace : WordTrace (prefixWord ++ tailWord_1367114) baseStart_1367114 baseEnd_1367114 := by
    simpa [prefixWord, tailWord_1367114, baseEnd_1367114] using wordTrace_append hprefix tailTrace_1367114
  have hstable : (prefixWord ++ tailWord_1367114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367114).length < 2 ^ (prefixWord ++ tailWord_1367114).sum := by decide
  have hdescent : baseEnd_1367114 < baseStart_1367114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367124 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1367124 : Nat := 118140960795 + 1367124 * 2 ^ 59
def prefixEnd_1367124 : Nat := 4983230072969 + 3 ^ 40 * 1367124 * 2
def baseEnd_1367124 : Nat := 233997242099138118254239

theorem tailTrace_1367124 : CollatzResearch.WordTrace tailWord_1367124 prefixEnd_1367124 233997242099138118254239 := by
  unfold tailWord_1367124
  simp only [CollatzResearch.WordTrace]
  refine ⟨24931554349575354517762213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33242072466100472690349617 24931554349575354517762213)
  ·
    refine ⟨4674666440545378972080415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24931554349575354517762213 4674666440545378972080415)
    ·
      refine ⟨7011999660818068458120623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674666440545378972080415 7011999660818068458120623)
      ·
        refine ⟨10517999491227102687180935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011999660818068458120623 10517999491227102687180935)
        ·
          refine ⟨15776999236840654030771403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10517999491227102687180935 15776999236840654030771403)
          ·
            refine ⟨23665498855260981046157105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15776999236840654030771403 23665498855260981046157105)
            ·
              refine ⟨17749124141445735784617829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23665498855260981046157105 17749124141445735784617829)
              ·
                refine ⟨3327960776521075459615843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17749124141445735784617829 3327960776521075459615843)
                ·
                  refine ⟨4991941164781613189423765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3327960776521075459615843 4991941164781613189423765)
                  ·
                    refine ⟨233997242099138118254239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4991941164781613189423765 233997242099138118254239)
                    ·
                      rfl

theorem cell23_1367124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1367124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367124 prefixEnd_1367124 := by exact prefixLift 1367124
  have htrace : WordTrace (prefixWord ++ tailWord_1367124) baseStart_1367124 baseEnd_1367124 := by
    simpa [prefixWord, tailWord_1367124, baseEnd_1367124] using wordTrace_append hprefix tailTrace_1367124
  have hstable : (prefixWord ++ tailWord_1367124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367124).length < 2 ^ (prefixWord ++ tailWord_1367124).sum := by decide
  have hdescent : baseEnd_1367124 < baseStart_1367124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367137 : List Nat := [1, 2, 3, 1, 1, 2, 13]
def baseStart_1367137 : Nat := 118140960795 + 1367137 * 2 ^ 59
def prefixEnd_1367137 : Nat := 4983230072969 + 3 ^ 40 * 1367137 * 2
def baseEnd_1367137 : Nat := 8666646932665713628397

theorem tailTrace_1367137 : CollatzResearch.WordTrace tailWord_1367137 prefixEnd_1367137 8666646932665713628397 := by
  unfold tailWord_1367137
  simp only [CollatzResearch.WordTrace]
  refine ⟨49863582848103612255747665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33242388565402408170498443 49863582848103612255747665)
  ·
    refine ⟨37397687136077709191810749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49863582848103612255747665 37397687136077709191810749)
    ·
      refine ⟨14024132676029140946929031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37397687136077709191810749 14024132676029140946929031)
      ·
        refine ⟨21036199014043711420393547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14024132676029140946929031 21036199014043711420393547)
        ·
          refine ⟨31554298521065567130590321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21036199014043711420393547 31554298521065567130590321)
          ·
            refine ⟨23665723890799175347942741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31554298521065567130590321 23665723890799175347942741)
            ·
              refine ⟨8666646932665713628397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 23665723890799175347942741 8666646932665713628397)
              ·
                rfl

theorem cell23_1367137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 13].length) (baseStart_1367137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367137 prefixEnd_1367137 := by exact prefixLift 1367137
  have htrace : WordTrace (prefixWord ++ tailWord_1367137) baseStart_1367137 baseEnd_1367137 := by
    simpa [prefixWord, tailWord_1367137, baseEnd_1367137] using wordTrace_append hprefix tailTrace_1367137
  have hstable : (prefixWord ++ tailWord_1367137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367137).length < 2 ^ (prefixWord ++ tailWord_1367137).sum := by decide
  have hdescent : baseEnd_1367137 < baseStart_1367137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367141 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_1367141 : Nat := 118140960795 + 1367141 * 2 ^ 59
def prefixEnd_1367141 : Nat := 4983230072969 + 3 ^ 40 * 1367141 * 2
def baseEnd_1367141 : Nat := 234000151822846929416713

theorem tailTrace_1367141 : CollatzResearch.WordTrace tailWord_1367141 prefixEnd_1367141 234000151822846929416713 := by
  unfold tailWord_1367141
  simp only [CollatzResearch.WordTrace]
  refine ⟨49863728740089120938893277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33242485826726080625928851 49863728740089120938893277)
  ·
    refine ⟨18698898277533420352084979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49863728740089120938893277 18698898277533420352084979)
    ·
      refine ⟨28048347416300130528127469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18698898277533420352084979 28048347416300130528127469)
      ·
        refine ⟨10518130281112548948047801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28048347416300130528127469 10518130281112548948047801)
        ·
          refine ⟨7888597710834411711035851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10518130281112548948047801 7888597710834411711035851)
          ·
            refine ⟨11832896566251617566553777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888597710834411711035851 11832896566251617566553777)
            ·
              refine ⟨8874672424688713174915333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11832896566251617566553777 8874672424688713174915333)
              ·
                refine ⟨1664001079629133720296625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8874672424688713174915333 1664001079629133720296625)
                ·
                  refine ⟨1248000809721850290222469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664001079629133720296625 1248000809721850290222469)
                  ·
                    refine ⟨234000151822846929416713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248000809721850290222469 234000151822846929416713)
                    ·
                      rfl

theorem cell23_1367141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_1367141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367141 prefixEnd_1367141 := by exact prefixLift 1367141
  have htrace : WordTrace (prefixWord ++ tailWord_1367141) baseStart_1367141 baseEnd_1367141 := by
    simpa [prefixWord, tailWord_1367141, baseEnd_1367141] using wordTrace_append hprefix tailTrace_1367141
  have hstable : (prefixWord ++ tailWord_1367141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367141).length < 2 ^ (prefixWord ++ tailWord_1367141).sum := by decide
  have hdescent : baseEnd_1367141 < baseStart_1367141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367154 : List Nat := [3, 2, 1, 2, 2, 1, 4, 8]
def baseStart_1367154 : Nat := 118140960795 + 1367154 * 2 ^ 59
def prefixEnd_1367154 : Nat := 4983230072969 + 3 ^ 40 * 1367154 * 2
def baseEnd_1367154 : Nat := 26000264100631453236577

theorem tailTrace_1367154 : CollatzResearch.WordTrace tailWord_1367154 prefixEnd_1367154 26000264100631453236577 := by
  unfold tailWord_1367154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466050722260506039779129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33242801926028016106077677 12466050722260506039779129)
  ·
    refine ⟨9349538041695379529834347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12466050722260506039779129 9349538041695379529834347)
    ·
      refine ⟨14024307062543069294751521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349538041695379529834347 14024307062543069294751521)
      ·
        refine ⟨10518230296907301971063641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14024307062543069294751521 10518230296907301971063641)
        ·
          refine ⟨7888672722680476478297731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10518230296907301971063641 7888672722680476478297731)
          ·
            refine ⟨11833009084020714717446597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888672722680476478297731 11833009084020714717446597)
            ·
              refine ⟨2218689203253884009521237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11833009084020714717446597 2218689203253884009521237)
              ·
                refine ⟨26000264100631453236577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2218689203253884009521237 26000264100631453236577)
                ·
                  rfl

theorem cell23_1367154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_1367154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367154 prefixEnd_1367154 := by exact prefixLift 1367154
  have htrace : WordTrace (prefixWord ++ tailWord_1367154) baseStart_1367154 baseEnd_1367154 := by
    simpa [prefixWord, tailWord_1367154, baseEnd_1367154] using wordTrace_append hprefix tailTrace_1367154
  have hstable : (prefixWord ++ tailWord_1367154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367154).length < 2 ^ (prefixWord ++ tailWord_1367154).sum := by decide
  have hdescent : baseEnd_1367154 < baseStart_1367154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367158 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1367158 : Nat := 118140960795 + 1367158 * 2 ^ 59
def prefixEnd_1367158 : Nat := 4983230072969 + 3 ^ 40 * 1367158 * 2
def baseEnd_1367158 : Nat := 234003061546555740579187

theorem tailTrace_1367158 : CollatzResearch.WordTrace tailWord_1367158 prefixEnd_1367158 234003061546555740579187 := by
  unfold tailWord_1367158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116521798814220802641383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33242899187351688561508085 3116521798814220802641383)
  ·
    refine ⟨4674782698221331203962075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116521798814220802641383 4674782698221331203962075)
    ·
      refine ⟨7012174047331996805943113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674782698221331203962075 7012174047331996805943113)
      ·
        refine ⟨5259130535498997604457335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7012174047331996805943113 5259130535498997604457335)
        ·
          refine ⟨7888695803248496406686003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259130535498997604457335 7888695803248496406686003)
          ·
            refine ⟨11833043704872744610029005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888695803248496406686003 11833043704872744610029005)
            ·
              refine ⟨4437391389327279228760877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11833043704872744610029005 4437391389327279228760877)
              ·
                refine ⟨1664021770997729710785329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4437391389327279228760877 1664021770997729710785329)
                ·
                  refine ⟨1248016328248297283088997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664021770997729710785329 1248016328248297283088997)
                  ·
                    refine ⟨234003061546555740579187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248016328248297283088997 234003061546555740579187)
                    ·
                      rfl

theorem cell23_1367158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1367158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367158 prefixEnd_1367158 := by exact prefixLift 1367158
  have htrace : WordTrace (prefixWord ++ tailWord_1367158) baseStart_1367158 baseEnd_1367158 := by
    simpa [prefixWord, tailWord_1367158, baseEnd_1367158] using wordTrace_append hprefix tailTrace_1367158
  have hstable : (prefixWord ++ tailWord_1367158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367158).length < 2 ^ (prefixWord ++ tailWord_1367158).sum := by decide
  have hdescent : baseEnd_1367158 < baseStart_1367158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367224 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1367224 : Nat := 118140960795 + 1367224 * 2 ^ 59
def prefixEnd_1367224 : Nat := 4983230072969 + 3 ^ 40 * 1367224 * 2
def baseEnd_1367224 : Nat := 702043074362863963512257

theorem tailTrace_1367224 : CollatzResearch.WordTrace tailWord_1367224 prefixEnd_1367224 702043074362863963512257 := by
  unfold tailWord_1367224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24933377999394213057082363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33244503999192284076109817 24933377999394213057082363)
  ·
    refine ⟨37400066999091319585623545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24933377999394213057082363 37400066999091319585623545)
    ·
      refine ⟨28050050249318489689217659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37400066999091319585623545 28050050249318489689217659)
      ·
        refine ⟨42075075373977734533826489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28050050249318489689217659 42075075373977734533826489)
        ·
          refine ⟨31556306530483300900369867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42075075373977734533826489 31556306530483300900369867)
          ·
            refine ⟨47334459795724951350554801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31556306530483300900369867 47334459795724951350554801)
            ·
              refine ⟨35500844846793713512916101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47334459795724951350554801 35500844846793713512916101)
              ·
                refine ⟨6656408408773821283671769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35500844846793713512916101 6656408408773821283671769)
                ·
                  refine ⟨4992306306580365962753827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6656408408773821283671769 4992306306580365962753827)
                  ·
                    refine ⟨7488459459870548944130741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4992306306580365962753827 7488459459870548944130741)
                    ·
                      refine ⟨702043074362863963512257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7488459459870548944130741 702043074362863963512257)
                      ·
                        rfl

theorem cell23_1367224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1367224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367224 prefixEnd_1367224 := by exact prefixLift 1367224
  have htrace : WordTrace (prefixWord ++ tailWord_1367224) baseStart_1367224 baseEnd_1367224 := by
    simpa [prefixWord, tailWord_1367224, baseEnd_1367224] using wordTrace_append hprefix tailTrace_1367224
  have hstable : (prefixWord ++ tailWord_1367224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367224).length < 2 ^ (prefixWord ++ tailWord_1367224).sum := by decide
  have hdescent : baseEnd_1367224 < baseStart_1367224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367242 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_1367242 : Nat := 118140960795 + 1367242 * 2 ^ 59
def prefixEnd_1367242 : Nat := 4983230072969 + 3 ^ 40 * 1367242 * 2
def baseEnd_1367242 : Nat := 702052317014644893087175

theorem tailTrace_1367242 : CollatzResearch.WordTrace tailWord_1367242 prefixEnd_1367242 702052317014644893087175 := by
  unfold tailWord_1367242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466853128180803797079995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33244941675148810125546653 12466853128180803797079995)
  ·
    refine ⟨18700279692271205695619993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12466853128180803797079995 18700279692271205695619993)
    ·
      refine ⟨14025209769203404271714995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18700279692271205695619993 14025209769203404271714995)
      ·
        refine ⟨21037814653805106407572493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14025209769203404271714995 21037814653805106407572493)
        ·
          refine ⟨7889180495176914902839685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21037814653805106407572493 7889180495176914902839685)
          ·
            refine ⟨1479221342845671544282441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7889180495176914902839685 1479221342845671544282441)
            ·
              refine ⟨1109416007134253658211831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479221342845671544282441 1109416007134253658211831)
              ·
                refine ⟨1664124010701380487317747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109416007134253658211831 1664124010701380487317747)
                ·
                  refine ⟨2496186016052070730976621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664124010701380487317747 2496186016052070730976621)
                  ·
                    refine ⟨936069756019526524116233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496186016052070730976621 936069756019526524116233)
                    ·
                      refine ⟨702052317014644893087175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936069756019526524116233 702052317014644893087175)
                      ·
                        rfl

theorem cell23_1367242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_1367242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367242 prefixEnd_1367242 := by exact prefixLift 1367242
  have htrace : WordTrace (prefixWord ++ tailWord_1367242) baseStart_1367242 baseEnd_1367242 := by
    simpa [prefixWord, tailWord_1367242, baseEnd_1367242] using wordTrace_append hprefix tailTrace_1367242
  have hstable : (prefixWord ++ tailWord_1367242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367242).length < 2 ^ (prefixWord ++ tailWord_1367242).sum := by decide
  have hdescent : baseEnd_1367242 < baseStart_1367242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367255 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_1367255 : Nat := 118140960795 + 1367255 * 2 ^ 59
def prefixEnd_1367255 : Nat := 4983230072969 + 3 ^ 40 * 1367255 * 2
def baseEnd_1367255 : Nat := 702058992263153342224615

theorem tailTrace_1367255 : CollatzResearch.WordTrace tailWord_1367255 prefixEnd_1367255 702058992263153342224615 := by
  unfold tailWord_1367255
  simp only [CollatzResearch.WordTrace]
  refine ⟨49867886661676118408543219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33245257774450745605695479 49867886661676118408543219)
  ·
    refine ⟨74801829992514177612814829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49867886661676118408543219 74801829992514177612814829)
    ·
      refine ⟨28050686247192816604805561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74801829992514177612814829 28050686247192816604805561)
      ·
        refine ⟨21038014685394612453604171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28050686247192816604805561 21038014685394612453604171)
        ·
          refine ⟨31557022028091918680406257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21038014685394612453604171 31557022028091918680406257)
          ·
            refine ⟨23667766521068939010304693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31557022028091918680406257 23667766521068939010304693)
            ·
              refine ⟨2218853111350213032216065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23667766521068939010304693 2218853111350213032216065)
              ·
                refine ⟨1664139833512659774162049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2218853111350213032216065 1664139833512659774162049)
                ·
                  refine ⟨1248104875134494830621537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664139833512659774162049 1248104875134494830621537)
                  ·
                    refine ⟨936078656350871122966153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248104875134494830621537 936078656350871122966153)
                    ·
                      refine ⟨702058992263153342224615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936078656350871122966153 702058992263153342224615)
                      ·
                        rfl

theorem cell23_1367255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_1367255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367255 prefixEnd_1367255 := by exact prefixLift 1367255
  have htrace : WordTrace (prefixWord ++ tailWord_1367255) baseStart_1367255 baseEnd_1367255 := by
    simpa [prefixWord, tailWord_1367255, baseEnd_1367255] using wordTrace_append hprefix tailTrace_1367255
  have hstable : (prefixWord ++ tailWord_1367255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367255).length < 2 ^ (prefixWord ++ tailWord_1367255).sum := by decide
  have hdescent : baseEnd_1367255 < baseStart_1367255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367272 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_1367272 : Nat := 118140960795 + 1367272 * 2 ^ 59
def prefixEnd_1367272 : Nat := 4983230072969 + 3 ^ 40 * 1367272 * 2
def baseEnd_1367272 : Nat := 702067721434279775712037

theorem tailTrace_1367272 : CollatzResearch.WordTrace tailWord_1367272 prefixEnd_1367272 702067721434279775712037 := by
  unfold tailWord_1367272
  simp only [CollatzResearch.WordTrace]
  refine ⟨24934253351307265155956035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33245671135076353541274713 24934253351307265155956035)
  ·
    refine ⟨37401380026960897733934053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24934253351307265155956035 37401380026960897733934053)
    ·
      refine ⟨7012758755055168325112635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37401380026960897733934053 7012758755055168325112635)
      ·
        refine ⟨10519138132582752487668953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7012758755055168325112635 10519138132582752487668953)
        ·
          refine ⟨7889353599437064365751715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10519138132582752487668953 7889353599437064365751715)
          ·
            refine ⟨11834030399155596548627573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7889353599437064365751715 11834030399155596548627573)
            ·
              refine ⟨1109440349920837176433835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11834030399155596548627573 1109440349920837176433835)
              ·
                refine ⟨1664160524881255764650753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109440349920837176433835 1664160524881255764650753)
                ·
                  refine ⟨1248120393660941823488065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664160524881255764650753 1248120393660941823488065)
                  ·
                    refine ⟨936090295245706367616049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248120393660941823488065 936090295245706367616049)
                    ·
                      refine ⟨702067721434279775712037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936090295245706367616049 702067721434279775712037)
                      ·
                        rfl

theorem cell23_1367272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_1367272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367272 prefixEnd_1367272 := by exact prefixLift 1367272
  have htrace : WordTrace (prefixWord ++ tailWord_1367272) baseStart_1367272 baseEnd_1367272 := by
    simpa [prefixWord, tailWord_1367272, baseEnd_1367272] using wordTrace_append hprefix tailTrace_1367272
  have hstable : (prefixWord ++ tailWord_1367272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367272).length < 2 ^ (prefixWord ++ tailWord_1367272).sum := by decide
  have hdescent : baseEnd_1367272 < baseStart_1367272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367372 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_1367372 : Nat := 118140960795 + 1367372 * 2 ^ 59
def prefixEnd_1367372 : Nat := 4983230072969 + 3 ^ 40 * 1367372 * 2
def baseEnd_1367372 : Nat := 234039689833243128153859

theorem tailTrace_1367372 : CollatzResearch.WordTrace tailWord_1367372 prefixEnd_1367372 234039689833243128153859 := by
  unfold tailWord_1367372
  simp only [CollatzResearch.WordTrace]
  refine ⟨24936077001126123695276185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33248102668168164927034913 24936077001126123695276185)
  ·
    refine ⟨18702057750844592771457139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24936077001126123695276185 18702057750844592771457139)
    ·
      refine ⟨28053086626266889157185709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18702057750844592771457139 28053086626266889157185709)
      ·
        refine ⟨10519907484850083433944641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28053086626266889157185709 10519907484850083433944641)
        ·
          refine ⟨7889930613637562575458481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10519907484850083433944641 7889930613637562575458481)
          ·
            refine ⟨5917447960228171931593861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7889930613637562575458481 5917447960228171931593861)
            ·
              refine ⟨1109521492542782237173849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5917447960228171931593861 1109521492542782237173849)
              ·
                refine ⟨832141119407086677880387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109521492542782237173849 832141119407086677880387)
                ·
                  refine ⟨1248211679110630016820581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832141119407086677880387 1248211679110630016820581)
                  ·
                    refine ⟨234039689833243128153859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248211679110630016820581 234039689833243128153859)
                    ·
                      rfl

theorem cell23_1367372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_1367372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367372 prefixEnd_1367372 := by exact prefixLift 1367372
  have htrace : WordTrace (prefixWord ++ tailWord_1367372) baseStart_1367372 baseEnd_1367372 := by
    simpa [prefixWord, tailWord_1367372, baseEnd_1367372] using wordTrace_append hprefix tailTrace_1367372
  have hstable : (prefixWord ++ tailWord_1367372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367372).length < 2 ^ (prefixWord ++ tailWord_1367372).sum := by decide
  have hdescent : baseEnd_1367372 < baseStart_1367372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367389 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1367389 : Nat := 118140960795 + 1367389 * 2 ^ 59
def prefixEnd_1367389 : Nat := 4983230072969 + 3 ^ 40 * 1367389 * 2
def baseEnd_1367389 : Nat := 234042599556951939316333

theorem tailTrace_1367389 : CollatzResearch.WordTrace tailWord_1367389 prefixEnd_1367389 234042599556951939316333 := by
  unfold tailWord_1367389
  simp only [CollatzResearch.WordTrace]
  refine ⟨49872774043190659293921221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33248516028793772862614147 49872774043190659293921221)
  ·
    refine ⟨9351145133098248617610229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49872774043190659293921221 9351145133098248617610229)
    ·
      refine ⟨876669856227960807900959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9351145133098248617610229 876669856227960807900959)
      ·
        refine ⟨1315004784341941211851439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876669856227960807900959 1315004784341941211851439)
        ·
          refine ⟨1972507176512911817777159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315004784341941211851439 1972507176512911817777159)
          ·
            refine ⟨2958760764769367726665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972507176512911817777159 2958760764769367726665739)
            ·
              refine ⟨4438141147154051589998609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958760764769367726665739 4438141147154051589998609)
              ·
                refine ⟨3328605860365538692498957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438141147154051589998609 3328605860365538692498957)
                ·
                  refine ⟨1248227197637077009687109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3328605860365538692498957 1248227197637077009687109)
                  ·
                    refine ⟨234042599556951939316333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248227197637077009687109 234042599556951939316333)
                    ·
                      rfl

theorem cell23_1367389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1367389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367389 prefixEnd_1367389 := by exact prefixLift 1367389
  have htrace : WordTrace (prefixWord ++ tailWord_1367389) baseStart_1367389 baseEnd_1367389 := by
    simpa [prefixWord, tailWord_1367389, baseEnd_1367389] using wordTrace_append hprefix tailTrace_1367389
  have hstable : (prefixWord ++ tailWord_1367389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367389).length < 2 ^ (prefixWord ++ tailWord_1367389).sum := by decide
  have hdescent : baseEnd_1367389 < baseStart_1367389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367395 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 3]
def baseStart_1367395 : Nat := 118140960795 + 1367395 * 2 ^ 59
def prefixEnd_1367395 : Nat := 4983230072969 + 3 ^ 40 * 1367395 * 2
def baseEnd_1367395 : Nat := 702130879554782794473971

theorem tailTrace_1367395 : CollatzResearch.WordTrace tailWord_1367395 prefixEnd_1367395 702130879554782794473971 := by
  unfold tailWord_1367395
  simp only [CollatzResearch.WordTrace]
  refine ⟨49872992881168922318639639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33248661920779281545759759 49872992881168922318639639)
  ·
    refine ⟨74809489321753383477959459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49872992881168922318639639 74809489321753383477959459)
    ·
      refine ⟨112214233982630075216939189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74809489321753383477959459 112214233982630075216939189)
      ·
        refine ⟨10520084435871569551588049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112214233982630075216939189 10520084435871569551588049)
        ·
          refine ⟨7890063326903677163691037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10520084435871569551588049 7890063326903677163691037)
          ·
            refine ⟨2958773747588878936384139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7890063326903677163691037 2958773747588878936384139)
            ·
              refine ⟨4438160621383318404576209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958773747588878936384139 4438160621383318404576209)
              ·
                refine ⟨3328620466037488803432157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438160621383318404576209 3328620466037488803432157)
                ·
                  refine ⟨1248232674764058301287059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3328620466037488803432157 1248232674764058301287059)
                  ·
                    refine ⟨1872349012146087451930589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248232674764058301287059 1872349012146087451930589)
                    ·
                      refine ⟨702130879554782794473971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872349012146087451930589 702130879554782794473971)
                      ·
                        rfl

theorem cell23_1367395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_1367395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367395 prefixEnd_1367395 := by exact prefixLift 1367395
  have htrace : WordTrace (prefixWord ++ tailWord_1367395) baseStart_1367395 baseEnd_1367395 := by
    simpa [prefixWord, tailWord_1367395, baseEnd_1367395] using wordTrace_append hprefix tailTrace_1367395
  have hstable : (prefixWord ++ tailWord_1367395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367395).length < 2 ^ (prefixWord ++ tailWord_1367395).sum := by decide
  have hdescent : baseEnd_1367395 < baseStart_1367395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367405 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1367405 : Nat := 118140960795 + 1367405 * 2 ^ 59
def prefixEnd_1367405 : Nat := 4983230072969 + 3 ^ 40 * 1367405 * 2
def baseEnd_1367405 : Nat := 702136014361327755348925

theorem tailTrace_1367405 : CollatzResearch.WordTrace tailWord_1367405 prefixEnd_1367405 702136014361327755348925 := by
  unfold tailWord_1367405
  simp only [CollatzResearch.WordTrace]
  refine ⟨49873357611132694026503669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33248905074088462684335779 49873357611132694026503669)
  ·
    refine ⟨4675627276043690064984719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49873357611132694026503669 4675627276043690064984719)
    ·
      refine ⟨7013440914065535097477079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4675627276043690064984719 7013440914065535097477079)
      ·
        refine ⟨10520161371098302646215619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7013440914065535097477079 10520161371098302646215619)
        ·
          refine ⟨15780242056647453969323429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10520161371098302646215619 15780242056647453969323429)
          ·
            refine ⟨2958795385621397619248143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15780242056647453969323429 2958795385621397619248143)
            ·
              refine ⟨4438193078432096428872215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958795385621397619248143 4438193078432096428872215)
              ·
                refine ⟨6657289617648144643308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4438193078432096428872215 6657289617648144643308323)
                ·
                  refine ⟨9985934426472216964962485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6657289617648144643308323 9985934426472216964962485)
                  ·
                    refine ⟨936181352481770340465233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9985934426472216964962485 936181352481770340465233)
                    ·
                      refine ⟨702136014361327755348925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936181352481770340465233 702136014361327755348925)
                      ·
                        rfl

theorem cell23_1367405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1367405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367405 prefixEnd_1367405 := by exact prefixLift 1367405
  have htrace : WordTrace (prefixWord ++ tailWord_1367405) baseStart_1367405 baseEnd_1367405 := by
    simpa [prefixWord, tailWord_1367405, baseEnd_1367405] using wordTrace_append hprefix tailTrace_1367405
  have hstable : (prefixWord ++ tailWord_1367405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367405).length < 2 ^ (prefixWord ++ tailWord_1367405).sum := by decide
  have hdescent : baseEnd_1367405 < baseStart_1367405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367418 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_1367418 : Nat := 118140960795 + 1367418 * 2 ^ 59
def prefixEnd_1367418 : Nat := 4983230072969 + 3 ^ 40 * 1367418 * 2
def baseEnd_1367418 : Nat := 702142689609836204486365

theorem tailTrace_1367418 : CollatzResearch.WordTrace tailWord_1367418 prefixEnd_1367418 702142689609836204486365 := by
  unfold tailWord_1367418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468457940021399311681727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33249221173390398164484605 12468457940021399311681727)
  ·
    refine ⟨18702686910032098967522591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12468457940021399311681727 18702686910032098967522591)
    ·
      refine ⟨28054030365048148451283887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18702686910032098967522591 28054030365048148451283887)
      ·
        refine ⟨42081045547572222676925831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28054030365048148451283887 42081045547572222676925831)
        ·
          refine ⟨63121568321358334015388747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42081045547572222676925831 63121568321358334015388747)
          ·
            refine ⟨94682352482037501023083121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63121568321358334015388747 94682352482037501023083121)
            ·
              refine ⟨71011764361528125767312341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94682352482037501023083121 71011764361528125767312341)
              ·
                refine ⟨1664338227223315447671383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71011764361528125767312341 1664338227223315447671383)
                ·
                  refine ⟨2496507340834973171507075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664338227223315447671383 2496507340834973171507075)
                  ·
                    refine ⟨3744761011252459757260613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2496507340834973171507075 3744761011252459757260613)
                    ·
                      refine ⟨702142689609836204486365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3744761011252459757260613 702142689609836204486365)
                      ·
                        rfl

theorem cell23_1367418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_1367418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367418 prefixEnd_1367418 := by exact prefixLift 1367418
  have htrace : WordTrace (prefixWord ++ tailWord_1367418) baseStart_1367418 baseEnd_1367418 := by
    simpa [prefixWord, tailWord_1367418, baseEnd_1367418] using wordTrace_append hprefix tailTrace_1367418
  have hstable : (prefixWord ++ tailWord_1367418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367418).length < 2 ^ (prefixWord ++ tailWord_1367418).sum := by decide
  have hdescent : baseEnd_1367418 < baseStart_1367418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367455 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1367455 : Nat := 118140960795 + 1367455 * 2 ^ 59
def prefixEnd_1367455 : Nat := 4983230072969 + 3 ^ 40 * 1367455 * 2
def baseEnd_1367455 : Nat := 702161688394052559723695

theorem tailTrace_1367455 : CollatzResearch.WordTrace tailWord_1367455 prefixEnd_1367455 702161688394052559723695 := by
  unfold tailWord_1367455
  simp only [CollatzResearch.WordTrace]
  refine ⟨49875181260951552565823819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33250120840634368377215879 49875181260951552565823819)
  ·
    refine ⟨74812771891427328848735729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49875181260951552565823819 74812771891427328848735729)
    ·
      refine ⟨56109578918570496636551797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74812771891427328848735729 56109578918570496636551797)
      ·
        refine ⟨5260273023615984059676731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56109578918570496636551797 5260273023615984059676731)
        ·
          refine ⟨7890409535423976089515097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260273023615984059676731 7890409535423976089515097)
          ·
            refine ⟨5917807151567982067136323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7890409535423976089515097 5917807151567982067136323)
            ·
              refine ⟨8876710727351973100704485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5917807151567982067136323 8876710727351973100704485)
              ·
                refine ⟨1664383261378494956382091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8876710727351973100704485 1664383261378494956382091)
                ·
                  refine ⟨2496574892067742434573137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664383261378494956382091 2496574892067742434573137)
                  ·
                    refine ⟨1872431169050806825929853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496574892067742434573137 1872431169050806825929853)
                    ·
                      refine ⟨702161688394052559723695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872431169050806825929853 702161688394052559723695)
                      ·
                        rfl

theorem cell23_1367455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1367455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367455 prefixEnd_1367455 := by exact prefixLift 1367455
  have htrace : WordTrace (prefixWord ++ tailWord_1367455) baseStart_1367455 baseEnd_1367455 := by
    simpa [prefixWord, tailWord_1367455, baseEnd_1367455] using wordTrace_append hprefix tailTrace_1367455
  have hstable : (prefixWord ++ tailWord_1367455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367455).length < 2 ^ (prefixWord ++ tailWord_1367455).sum := by decide
  have hdescent : baseEnd_1367455 < baseStart_1367455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367458 : List Nat := [3, 3, 1, 2, 1, 3, 1, 9]
def baseStart_1367458 : Nat := 118140960795 + 1367458 * 2 ^ 59
def prefixEnd_1367458 : Nat := 4983230072969 + 3 ^ 40 * 1367458 * 2
def baseEnd_1367458 : Nat := 26006045512445038814303

theorem tailTrace_1367458 : CollatzResearch.WordTrace tailWord_1367458 prefixEnd_1367458 26006045512445038814303 := by
  unfold tailWord_1367458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12468822669985171019545757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33250193786627122718788685 12468822669985171019545757)
  ·
    refine ⟨4675808501244439132329659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12468822669985171019545757 4675808501244439132329659)
    ·
      refine ⟨7013712751866658698494489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4675808501244439132329659 7013712751866658698494489)
      ·
        refine ⟨5260284563899994023870867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7013712751866658698494489 5260284563899994023870867)
        ·
          refine ⟨7890426845849991035806301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260284563899994023870867 7890426845849991035806301)
          ·
            refine ⟨2958910067193746638427363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7890426845849991035806301 2958910067193746638427363)
            ·
              refine ⟨4438365100790619957641045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958910067193746638427363 4438365100790619957641045)
              ·
                refine ⟨26006045512445038814303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4438365100790619957641045 26006045512445038814303)
                ·
                  rfl

theorem cell23_1367458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_1367458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367458 prefixEnd_1367458 := by exact prefixLift 1367458
  have htrace : WordTrace (prefixWord ++ tailWord_1367458) baseStart_1367458 baseEnd_1367458 := by
    simpa [prefixWord, tailWord_1367458, baseEnd_1367458] using wordTrace_append hprefix tailTrace_1367458
  have hstable : (prefixWord ++ tailWord_1367458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367458).length < 2 ^ (prefixWord ++ tailWord_1367458).sum := by decide
  have hdescent : baseEnd_1367458 < baseStart_1367458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367468 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_1367468 : Nat := 118140960795 + 1367468 * 2 ^ 59
def prefixEnd_1367468 : Nat := 4983230072969 + 3 ^ 40 * 1367468 * 2
def baseEnd_1367468 : Nat := 702168363642561008861135

theorem tailTrace_1367468 : CollatzResearch.WordTrace tailWord_1367468 prefixEnd_1367468 702168363642561008861135 := by
  unfold tailWord_1367468
  simp only [CollatzResearch.WordTrace]
  refine ⟨24937827704952227893023529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33250436939936303857364705 24937827704952227893023529)
  ·
    refine ⟨18703370778714170919767647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24937827704952227893023529 18703370778714170919767647)
    ·
      refine ⟨28055056168071256379651471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18703370778714170919767647 28055056168071256379651471)
      ·
        refine ⟨42082584252106884569477207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28055056168071256379651471 42082584252106884569477207)
        ·
          refine ⟨63123876378160326854215811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42082584252106884569477207 63123876378160326854215811)
          ·
            refine ⟨94685814567240490281323717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63123876378160326854215811 94685814567240490281323717)
            ·
              refine ⟨17753590231357591927748197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94685814567240490281323717 17753590231357591927748197)
              ·
                refine ⟨3328798168379548486452787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17753590231357591927748197 3328798168379548486452787)
                ·
                  refine ⟨4993197252569322729679181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3328798168379548486452787 4993197252569322729679181)
                  ·
                    refine ⟨1872448969713496023629693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4993197252569322729679181 1872448969713496023629693)
                    ·
                      refine ⟨702168363642561008861135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872448969713496023629693 702168363642561008861135)
                      ·
                        rfl

theorem cell23_1367468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_1367468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367468 prefixEnd_1367468 := by exact prefixLift 1367468
  have htrace : WordTrace (prefixWord ++ tailWord_1367468) baseStart_1367468 baseEnd_1367468 := by
    simpa [prefixWord, tailWord_1367468, baseEnd_1367468] using wordTrace_append hprefix tailTrace_1367468
  have hstable : (prefixWord ++ tailWord_1367468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367468).length < 2 ^ (prefixWord ++ tailWord_1367468).sum := by decide
  have hdescent : baseEnd_1367468 < baseStart_1367468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367485 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_1367485 : Nat := 118140960795 + 1367485 * 2 ^ 59
def prefixEnd_1367485 : Nat := 4983230072969 + 3 ^ 40 * 1367485 * 2
def baseEnd_1367485 : Nat := 702177092813687442348557

theorem tailTrace_1367485 : CollatzResearch.WordTrace tailWord_1367485 prefixEnd_1367485 702177092813687442348557 := by
  unfold tailWord_1367485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49876275450842867689415909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33250850300561911792943939 49876275450842867689415909)
  ·
    refine ⟨9351801647033037691765483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49876275450842867689415909 9351801647033037691765483)
    ·
      refine ⟨14027702470549556537648225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351801647033037691765483 14027702470549556537648225)
      ·
        refine ⟨10520776852912167403236169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14027702470549556537648225 10520776852912167403236169)
        ·
          refine ⟨7890582639684125552427127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10520776852912167403236169 7890582639684125552427127)
          ·
            refine ⟨11835873959526188328640691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7890582639684125552427127 11835873959526188328640691)
            ·
              refine ⟨17753810939289282492961037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11835873959526188328640691 17753810939289282492961037)
              ·
                refine ⟨6657679102233480934860389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17753810939289282492961037 6657679102233480934860389)
                ·
                  refine ⟨1248314831668777675286323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6657679102233480934860389 1248314831668777675286323)
                  ·
                    refine ⟨1872472247503166512929485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248314831668777675286323 1872472247503166512929485)
                    ·
                      refine ⟨702177092813687442348557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872472247503166512929485 702177092813687442348557)
                      ·
                        rfl

theorem cell23_1367485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_1367485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367485 prefixEnd_1367485 := by exact prefixLift 1367485
  have htrace : WordTrace (prefixWord ++ tailWord_1367485) baseStart_1367485 baseEnd_1367485 := by
    simpa [prefixWord, tailWord_1367485, baseEnd_1367485] using wordTrace_append hprefix tailTrace_1367485
  have hstable : (prefixWord ++ tailWord_1367485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367485).length < 2 ^ (prefixWord ++ tailWord_1367485).sum := by decide
  have hdescent : baseEnd_1367485 < baseStart_1367485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367495 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_1367495 : Nat := 118140960795 + 1367495 * 2 ^ 59
def prefixEnd_1367495 : Nat := 4983230072969 + 3 ^ 40 * 1367495 * 2
def baseEnd_1367495 : Nat := 702182227620232403223511

theorem tailTrace_1367495 : CollatzResearch.WordTrace tailWord_1367495 prefixEnd_1367495 702182227620232403223511 := by
  unfold tailWord_1367495
  simp only [CollatzResearch.WordTrace]
  refine ⟨49876640180806639397279939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33251093453871092931519959 49876640180806639397279939)
  ·
    refine ⟨74814960271209959095919909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49876640180806639397279939 74814960271209959095919909)
    ·
      refine ⟨14027805050851867330484983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74814960271209959095919909 14027805050851867330484983)
      ·
        refine ⟨21041707576277800995727475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14027805050851867330484983 21041707576277800995727475)
        ·
          refine ⟨31562561364416701493591213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21041707576277800995727475 31562561364416701493591213)
          ·
            refine ⟨11835960511656263060096705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31562561364416701493591213 11835960511656263060096705)
            ·
              refine ⟨8876970383742197295072529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11835960511656263060096705 8876970383742197295072529)
              ·
                refine ⟨6657727787806647971304397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8876970383742197295072529 6657727787806647971304397)
                ·
                  refine ⟨2496647920427492989239149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6657727787806647971304397 2496647920427492989239149)
                  ·
                    refine ⟨936242970160309870964681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496647920427492989239149 936242970160309870964681)
                    ·
                      refine ⟨702182227620232403223511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936242970160309870964681 702182227620232403223511)
                      ·
                        rfl

theorem cell23_1367495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_1367495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367495 prefixEnd_1367495 := by exact prefixLift 1367495
  have htrace : WordTrace (prefixWord ++ tailWord_1367495) baseStart_1367495 baseEnd_1367495 := by
    simpa [prefixWord, tailWord_1367495, baseEnd_1367495] using wordTrace_append hprefix tailTrace_1367495
  have hstable : (prefixWord ++ tailWord_1367495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367495).length < 2 ^ (prefixWord ++ tailWord_1367495).sum := by decide
  have hdescent : baseEnd_1367495 < baseStart_1367495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367512 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_1367512 : Nat := 118140960795 + 1367512 * 2 ^ 59
def prefixEnd_1367512 : Nat := 4983230072969 + 3 ^ 40 * 1367512 * 2
def baseEnd_1367512 : Nat := 702190956791358836710933

theorem tailTrace_1367512 : CollatzResearch.WordTrace tailWord_1367512 prefixEnd_1367512 702190956791358836710933 := by
  unfold tailWord_1367512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938630110872525650324395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33251506814496700867099193 24938630110872525650324395)
  ·
    refine ⟨37407945166308788475486593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24938630110872525650324395 37407945166308788475486593)
    ·
      refine ⟨28055958874731591356614945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37407945166308788475486593 28055958874731591356614945)
      ·
        refine ⟨21041969156048693517461209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28055958874731591356614945 21041969156048693517461209)
        ·
          refine ⟨15781476867036520138095907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21041969156048693517461209 15781476867036520138095907)
          ·
            refine ⟨23672215300554780207143861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15781476867036520138095907 23672215300554780207143861)
            ·
              refine ⟨2219270184427010644419737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23672215300554780207143861 2219270184427010644419737)
              ·
                refine ⟨1664452638320257983314803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219270184427010644419737 1664452638320257983314803)
                ·
                  refine ⟨2496678957480386974972205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664452638320257983314803 2496678957480386974972205)
                  ·
                    refine ⟨936254609055145115614577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496678957480386974972205 936254609055145115614577)
                    ·
                      refine ⟨702190956791358836710933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936254609055145115614577 702190956791358836710933)
                      ·
                        rfl

theorem cell23_1367512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_1367512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367512 prefixEnd_1367512 := by exact prefixLift 1367512
  have htrace : WordTrace (prefixWord ++ tailWord_1367512) baseStart_1367512 baseEnd_1367512 := by
    simpa [prefixWord, tailWord_1367512, baseEnd_1367512] using wordTrace_append hprefix tailTrace_1367512
  have hstable : (prefixWord ++ tailWord_1367512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367512).length < 2 ^ (prefixWord ++ tailWord_1367512).sum := by decide
  have hdescent : baseEnd_1367512 < baseStart_1367512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367528 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1367528 : Nat := 118140960795 + 1367528 * 2 ^ 59
def prefixEnd_1367528 : Nat := 4983230072969 + 3 ^ 40 * 1367528 * 2
def baseEnd_1367528 : Nat := 702199172481830774110859

theorem tailTrace_1367528 : CollatzResearch.WordTrace tailWord_1367528 prefixEnd_1367528 702199172481830774110859 := by
  unfold tailWord_1367528
  simp only [CollatzResearch.WordTrace]
  refine ⟨24938921894843543016615619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33251895859791390688820825 24938921894843543016615619)
  ·
    refine ⟨37408382842265314524923429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24938921894843543016615619 37408382842265314524923429)
    ·
      refine ⟨7014071782924746473423143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37408382842265314524923429 7014071782924746473423143)
      ·
        refine ⟨10521107674387119710134715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7014071782924746473423143 10521107674387119710134715)
        ·
          refine ⟨15781661511580679565202073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10521107674387119710134715 15781661511580679565202073)
          ·
            refine ⟨11836246133685509673901555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15781661511580679565202073 11836246133685509673901555)
            ·
              refine ⟨17754369200528264510852333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11836246133685509673901555 17754369200528264510852333)
              ·
                refine ⟨6657888450198099191569625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17754369200528264510852333 6657888450198099191569625)
                ·
                  refine ⟨4993416337648574393677219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6657888450198099191569625 4993416337648574393677219)
                  ·
                    refine ⟨7490124506472861590515829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4993416337648574393677219 7490124506472861590515829)
                    ·
                      refine ⟨702199172481830774110859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7490124506472861590515829 702199172481830774110859)
                      ·
                        rfl

theorem cell23_1367528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1367528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367528 prefixEnd_1367528 := by exact prefixLift 1367528
  have htrace : WordTrace (prefixWord ++ tailWord_1367528) baseStart_1367528 baseEnd_1367528 := by
    simpa [prefixWord, tailWord_1367528, baseEnd_1367528] using wordTrace_append hprefix tailTrace_1367528
  have hstable : (prefixWord ++ tailWord_1367528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367528).length < 2 ^ (prefixWord ++ tailWord_1367528).sum := by decide
  have hdescent : baseEnd_1367528 < baseStart_1367528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367531 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 11]
def baseStart_1367531 : Nat := 118140960795 + 1367531 * 2 ^ 59
def prefixEnd_1367531 : Nat := 4983230072969 + 3 ^ 40 * 1367531 * 2
def baseEnd_1367531 : Nat := 78022301435977140263705

theorem tailTrace_1367531 : CollatzResearch.WordTrace tailWord_1367531 prefixEnd_1367531 78022301435977140263705 := by
  unfold tailWord_1367531
  simp only [CollatzResearch.WordTrace]
  refine ⟨49877953208676217545590447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33251968805784145030393631 49877953208676217545590447)
  ·
    refine ⟨74816929813014326318385671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49877953208676217545590447 74816929813014326318385671)
    ·
      refine ⟨112225394719521489477578507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74816929813014326318385671 112225394719521489477578507)
      ·
        refine ⟨168338092079282234216367761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112225394719521489477578507 168338092079282234216367761)
        ·
          refine ⟨126253569059461675662275821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168338092079282234216367761 126253569059461675662275821)
          ·
            refine ⟨47345088397298128373353433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126253569059461675662275821 47345088397298128373353433)
            ·
              refine ⟨35508816297973596280015075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47345088397298128373353433 35508816297973596280015075)
              ·
                refine ⟨53263224446960394420022613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35508816297973596280015075 53263224446960394420022613)
                ·
                  refine ⟨78022301435977140263705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 53263224446960394420022613 78022301435977140263705)
                  ·
                    rfl

theorem cell23_1367531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 11].length) (baseStart_1367531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367531 prefixEnd_1367531 := by exact prefixLift 1367531
  have htrace : WordTrace (prefixWord ++ tailWord_1367531) baseStart_1367531 baseEnd_1367531 := by
    simpa [prefixWord, tailWord_1367531, baseEnd_1367531] using wordTrace_append hprefix tailTrace_1367531
  have hstable : (prefixWord ++ tailWord_1367531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367531).length < 2 ^ (prefixWord ++ tailWord_1367531).sum := by decide
  have hdescent : baseEnd_1367531 < baseStart_1367531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367559 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_1367559 : Nat := 118140960795 + 1367559 * 2 ^ 59
def prefixEnd_1367559 : Nat := 4983230072969 + 3 ^ 40 * 1367559 * 2
def baseEnd_1367559 : Nat := 702215090382120152823217

theorem tailTrace_1367559 : CollatzResearch.WordTrace tailWord_1367559 prefixEnd_1367559 702215090382120152823217 := by
  unfold tailWord_1367559
  simp only [CollatzResearch.WordTrace]
  refine ⟨49878974452574778327609731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33252649635049852218406487 49878974452574778327609731)
  ·
    refine ⟨74818461678862167491414597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49878974452574778327609731 74818461678862167491414597)
    ·
      refine ⟨14028461564786656404640237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74818461678862167491414597 14028461564786656404640237)
      ·
        refine ⟨5260673086794996151740089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14028461564786656404640237 5260673086794996151740089)
        ·
          refine ⟨3945504815096247113805067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5260673086794996151740089 3945504815096247113805067)
          ·
            refine ⟨5918257222644370670707601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945504815096247113805067 5918257222644370670707601)
            ·
              refine ⟨4438692916983278003030701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5918257222644370670707601 4438692916983278003030701)
              ·
                refine ⟨1664509843868729251136513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4438692916983278003030701 1664509843868729251136513)
                ·
                  refine ⟨1248382382901546938352385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664509843868729251136513 1248382382901546938352385)
                  ·
                    refine ⟨936286787176160203764289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248382382901546938352385 936286787176160203764289)
                    ·
                      refine ⟨702215090382120152823217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936286787176160203764289 702215090382120152823217)
                      ·
                        rfl

theorem cell23_1367559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_1367559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367559 prefixEnd_1367559 := by exact prefixLift 1367559
  have htrace : WordTrace (prefixWord ++ tailWord_1367559) baseStart_1367559 baseEnd_1367559 := by
    simpa [prefixWord, tailWord_1367559, baseEnd_1367559] using wordTrace_append hprefix tailTrace_1367559
  have hstable : (prefixWord ++ tailWord_1367559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367559).length < 2 ^ (prefixWord ++ tailWord_1367559).sum := by decide
  have hdescent : baseEnd_1367559 < baseStart_1367559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367652 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_1367652 : Nat := 118140960795 + 1367652 * 2 ^ 59
def prefixEnd_1367652 : Nat := 4983230072969 + 3 ^ 40 * 1367652 * 2
def baseEnd_1367652 : Nat := 702262844082988288960289

theorem tailTrace_1367652 : CollatzResearch.WordTrace tailWord_1367652 prefixEnd_1367652 702262844082988288960289 := by
  unfold tailWord_1367652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24941183220618927605372605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33254910960825236807163473 24941183220618927605372605)
  ·
    refine ⟨9352943707732097852014727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24941183220618927605372605 9352943707732097852014727)
    ·
      refine ⟨14029415561598146778022091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9352943707732097852014727 14029415561598146778022091)
      ·
        refine ⟨21044123342397220167033137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14029415561598146778022091 21044123342397220167033137)
        ·
          refine ⟨15783092506797915125274853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21044123342397220167033137 15783092506797915125274853)
          ·
            refine ⟨2959329845024609085989035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15783092506797915125274853 2959329845024609085989035)
            ·
              refine ⟨4438994767536913628983553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959329845024609085989035 4438994767536913628983553)
              ·
                refine ⟨3329246075652685221737665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4438994767536913628983553 3329246075652685221737665)
                ·
                  refine ⟨2496934556739513916303249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329246075652685221737665 2496934556739513916303249)
                  ·
                    refine ⟨1872700917554635437227437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496934556739513916303249 1872700917554635437227437)
                    ·
                      refine ⟨702262844082988288960289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872700917554635437227437 702262844082988288960289)
                      ·
                        rfl

theorem cell23_1367652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_1367652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367652 prefixEnd_1367652 := by exact prefixLift 1367652
  have htrace : WordTrace (prefixWord ++ tailWord_1367652) baseStart_1367652 baseEnd_1367652 := by
    simpa [prefixWord, tailWord_1367652, baseEnd_1367652] using wordTrace_append hprefix tailTrace_1367652
  have hstable : (prefixWord ++ tailWord_1367652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367652).length < 2 ^ (prefixWord ++ tailWord_1367652).sum := by decide
  have hdescent : baseEnd_1367652 < baseStart_1367652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367685 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_1367685 : Nat := 118140960795 + 1367685 * 2 ^ 59
def prefixEnd_1367685 : Nat := 4983230072969 + 3 ^ 40 * 1367685 * 2
def baseEnd_1367685 : Nat := 234093262981528886615879

theorem tailTrace_1367685 : CollatzResearch.WordTrace tailWord_1367685 prefixEnd_1367685 234093262981528886615879 := by
  unfold tailWord_1367685
  simp only [CollatzResearch.WordTrace]
  refine ⟨49883570050118301846696509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33255713366745534564464339 49883570050118301846696509)
  ·
    refine ⟨18706338768794363192511191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49883570050118301846696509 18706338768794363192511191)
    ·
      refine ⟨28059508153191544788766787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18706338768794363192511191 28059508153191544788766787)
      ·
        refine ⟨42089262229787317183150181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28059508153191544788766787 42089262229787317183150181)
        ·
          refine ⟨7891736668085121971840659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42089262229787317183150181 7891736668085121971840659)
          ·
            refine ⟨11837605002127682957760989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7891736668085121971840659 11837605002127682957760989)
            ·
              refine ⟨4439101875797881109160371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11837605002127682957760989 4439101875797881109160371)
              ·
                refine ⟨6658652813696821663740557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4439101875797881109160371 6658652813696821663740557)
                ·
                  refine ⟨2496994805136308123902709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6658652813696821663740557 2496994805136308123902709)
                  ·
                    refine ⟨234093262981528886615879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2496994805136308123902709 234093262981528886615879)
                    ·
                      rfl

theorem cell23_1367685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_1367685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367685 prefixEnd_1367685 := by exact prefixLift 1367685
  have htrace : WordTrace (prefixWord ++ tailWord_1367685) baseStart_1367685 baseEnd_1367685 := by
    simpa [prefixWord, tailWord_1367685, baseEnd_1367685] using wordTrace_append hprefix tailTrace_1367685
  have hstable : (prefixWord ++ tailWord_1367685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367685).length < 2 ^ (prefixWord ++ tailWord_1367685).sum := by decide
  have hdescent : baseEnd_1367685 < baseStart_1367685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367716 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_1367716 : Nat := 118140960795 + 1367716 * 2 ^ 59
def prefixEnd_1367716 : Nat := 4983230072969 + 3 ^ 40 * 1367716 * 2
def baseEnd_1367716 : Nat := 702295706844876038559995

theorem tailTrace_1367716 : CollatzResearch.WordTrace tailWord_1367716 prefixEnd_1367716 702295706844876038559995 := by
  unfold tailWord_1367716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24942350356502997070537501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33256467142003996094050001 24942350356502997070537501)
  ·
    refine ⟨9353381383688623901451563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24942350356502997070537501 9353381383688623901451563)
    ·
      refine ⟨14030072075532935852177345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9353381383688623901451563 14030072075532935852177345)
      ·
        refine ⟨10522554056649701889133009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14030072075532935852177345 10522554056649701889133009)
        ·
          refine ⟨7891915542487276416849757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10522554056649701889133009 7891915542487276416849757)
          ·
            refine ⟨2959468328432728656318659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7891915542487276416849757 2959468328432728656318659)
            ·
              refine ⟨4439202492649092984477989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2959468328432728656318659 4439202492649092984477989)
              ·
                refine ⟨832350467371704934589623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4439202492649092984477989 832350467371704934589623)
                ·
                  refine ⟨1248525701057557401884435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832350467371704934589623 1248525701057557401884435)
                  ·
                    refine ⟨1872788551586336102826653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248525701057557401884435 1872788551586336102826653)
                    ·
                      refine ⟨702295706844876038559995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872788551586336102826653 702295706844876038559995)
                      ·
                        rfl

theorem cell23_1367716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_1367716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367716 prefixEnd_1367716 := by exact prefixLift 1367716
  have htrace : WordTrace (prefixWord ++ tailWord_1367716) baseStart_1367716 baseEnd_1367716 := by
    simpa [prefixWord, tailWord_1367716, baseEnd_1367716] using wordTrace_append hprefix tailTrace_1367716
  have hstable : (prefixWord ++ tailWord_1367716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367716).length < 2 ^ (prefixWord ++ tailWord_1367716).sum := by decide
  have hdescent : baseEnd_1367716 < baseStart_1367716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367750 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1367750 : Nat := 118140960795 + 1367750 * 2 ^ 59
def prefixEnd_1367750 : Nat := 4983230072969 + 3 ^ 40 * 1367750 * 2
def baseEnd_1367750 : Nat := 702313165187128905534839

theorem tailTrace_1367750 : CollatzResearch.WordTrace tailWord_1367750 prefixEnd_1367750 702313165187128905534839 := by
  unfold tailWord_1367750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558935649840088060869147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33257293863255211965208469 1558935649840088060869147)
  ·
    refine ⟨2338403474760132091303721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1558935649840088060869147 2338403474760132091303721)
    ·
      refine ⟨1753802606070099068477791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338403474760132091303721 1753802606070099068477791)
      ·
        refine ⟨2630703909105148602716687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753802606070099068477791 2630703909105148602716687)
        ·
          refine ⟨3946055863657722904075031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630703909105148602716687 3946055863657722904075031)
          ·
            refine ⟨5919083795486584356112547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946055863657722904075031 5919083795486584356112547)
            ·
              refine ⟨8878625693229876534168821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919083795486584356112547 8878625693229876534168821)
              ·
                refine ⟨832371158740300925078327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8878625693229876534168821 832371158740300925078327)
                ·
                  refine ⟨1248556738110451387617491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832371158740300925078327 1248556738110451387617491)
                  ·
                    refine ⟨1872835107165677081426237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248556738110451387617491 1872835107165677081426237)
                    ·
                      refine ⟨702313165187128905534839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872835107165677081426237 702313165187128905534839)
                      ·
                        rfl

theorem cell23_1367750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1367750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367750 prefixEnd_1367750 := by exact prefixLift 1367750
  have htrace : WordTrace (prefixWord ++ tailWord_1367750) baseStart_1367750 baseEnd_1367750 := by
    simpa [prefixWord, tailWord_1367750, baseEnd_1367750] using wordTrace_append hprefix tailTrace_1367750
  have hstable : (prefixWord ++ tailWord_1367750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367750).length < 2 ^ (prefixWord ++ tailWord_1367750).sum := by decide
  have hdescent : baseEnd_1367750 < baseStart_1367750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367783 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1367783 : Nat := 118140960795 + 1367783 * 2 ^ 59
def prefixEnd_1367783 : Nat := 4983230072969 + 3 ^ 40 * 1367783 * 2
def baseEnd_1367783 : Nat := 234110036682909092140729

theorem tailTrace_1367783 : CollatzResearch.WordTrace tailWord_1367783 prefixEnd_1367783 234110036682909092140729 := by
  unfold tailWord_1367783
  simp only [CollatzResearch.WordTrace]
  refine ⟨49887144403763264583764003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33258096269175509722509335 49887144403763264583764003)
  ·
    refine ⟨74830716605644896875646005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49887144403763264583764003 74830716605644896875646005)
    ·
      refine ⟨7015379681779209082091813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74830716605644896875646005 7015379681779209082091813)
      ·
        refine ⟨1315383690333601702892215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7015379681779209082091813 1315383690333601702892215)
        ·
          refine ⟨1973075535500402554338323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315383690333601702892215 1973075535500402554338323)
          ·
            refine ⟨2959613303250603831507485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973075535500402554338323 2959613303250603831507485)
            ·
              refine ⟨1109854988718976436815307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959613303250603831507485 1109854988718976436815307)
              ·
                refine ⟨1664782483078464655222961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109854988718976436815307 1664782483078464655222961)
                ·
                  refine ⟨1248586862308848491417221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1664782483078464655222961 1248586862308848491417221)
                  ·
                    refine ⟨234110036682909092140729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1248586862308848491417221 234110036682909092140729)
                    ·
                      rfl

theorem cell23_1367783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1367783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367783 prefixEnd_1367783 := by exact prefixLift 1367783
  have htrace : WordTrace (prefixWord ++ tailWord_1367783) baseStart_1367783 baseEnd_1367783 := by
    simpa [prefixWord, tailWord_1367783, baseEnd_1367783] using wordTrace_append hprefix tailTrace_1367783
  have hstable : (prefixWord ++ tailWord_1367783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367783).length < 2 ^ (prefixWord ++ tailWord_1367783).sum := by decide
  have hdescent : baseEnd_1367783 < baseStart_1367783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367789 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1367789 : Nat := 118140960795 + 1367789 * 2 ^ 59
def prefixEnd_1367789 : Nat := 4983230072969 + 3 ^ 40 * 1367789 * 2
def baseEnd_1367789 : Nat := 702333190932654252947159

theorem tailTrace_1367789 : CollatzResearch.WordTrace tailWord_1367789 prefixEnd_1367789 702333190932654252947159 := by
  unfold tailWord_1367789
  simp only [CollatzResearch.WordTrace]
  refine ⟨49887363241741527608482421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33258242161161018405654947 49887363241741527608482421)
  ·
    refine ⟨4676940303913268213295227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49887363241741527608482421 4676940303913268213295227)
    ·
      refine ⟨7015410455869902319942841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676940303913268213295227 7015410455869902319942841)
      ·
        refine ⟨5261557841902426739957131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7015410455869902319942841 5261557841902426739957131)
        ·
          refine ⟨7892336762853640109935697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5261557841902426739957131 7892336762853640109935697)
          ·
            refine ⟨5919252572140230082451773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7892336762853640109935697 5919252572140230082451773)
            ·
              refine ⟨2219719714552586280919415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5919252572140230082451773 2219719714552586280919415)
              ·
                refine ⟨3329579571828879421379123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219719714552586280919415 3329579571828879421379123)
                ·
                  refine ⟨4994369357743319132068685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329579571828879421379123 4994369357743319132068685)
                  ·
                    refine ⟨1872888509153744674525757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4994369357743319132068685 1872888509153744674525757)
                    ·
                      refine ⟨702333190932654252947159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1872888509153744674525757 702333190932654252947159)
                      ·
                        rfl

theorem cell23_1367789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1367789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367789 prefixEnd_1367789 := by exact prefixLift 1367789
  have htrace : WordTrace (prefixWord ++ tailWord_1367789) baseStart_1367789 baseEnd_1367789 := by
    simpa [prefixWord, tailWord_1367789, baseEnd_1367789] using wordTrace_append hprefix tailTrace_1367789
  have hstable : (prefixWord ++ tailWord_1367789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367789).length < 2 ^ (prefixWord ++ tailWord_1367789).sum := by decide
  have hdescent : baseEnd_1367789 < baseStart_1367789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367795 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4]
def baseStart_1367795 : Nat := 118140960795 + 1367795 * 2 ^ 59
def prefixEnd_1367795 : Nat := 4983230072969 + 3 ^ 40 * 1367795 * 2
def baseEnd_1367795 : Nat := 702336271816581229472131

theorem tailTrace_1367795 : CollatzResearch.WordTrace tailWord_1367795 prefixEnd_1367795 702336271816581229472131 := by
  unfold tailWord_1367795
  simp only [CollatzResearch.WordTrace]
  refine ⟨49887582079719790633200839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33258388053146527088800559 49887582079719790633200839)
  ·
    refine ⟨74831373119579685949801259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49887582079719790633200839 74831373119579685949801259)
    ·
      refine ⟨112247059679369528924701889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74831373119579685949801259 112247059679369528924701889)
      ·
        refine ⟨84185294759527146693526417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112247059679369528924701889 84185294759527146693526417)
        ·
          refine ⟨63138971069645360020144813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84185294759527146693526417 63138971069645360020144813)
          ·
            refine ⟨23677114151117010007554305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63138971069645360020144813 23677114151117010007554305)
            ·
              refine ⟨17757835613337757505665729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23677114151117010007554305 17757835613337757505665729)
              ·
                refine ⟨13318376710003318129249297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17757835613337757505665729 13318376710003318129249297)
                ·
                  refine ⟨9988782532502488596936973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13318376710003318129249297 9988782532502488596936973)
                  ·
                    refine ⟨3745793449688433223851365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9988782532502488596936973 3745793449688433223851365)
                    ·
                      refine ⟨702336271816581229472131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3745793449688433223851365 702336271816581229472131)
                      ·
                        rfl

theorem cell23_1367795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_1367795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367795 prefixEnd_1367795 := by exact prefixLift 1367795
  have htrace : WordTrace (prefixWord ++ tailWord_1367795) baseStart_1367795 baseEnd_1367795 := by
    simpa [prefixWord, tailWord_1367795, baseEnd_1367795] using wordTrace_append hprefix tailTrace_1367795
  have hstable : (prefixWord ++ tailWord_1367795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367795).length < 2 ^ (prefixWord ++ tailWord_1367795).sum := by decide
  have hdescent : baseEnd_1367795 < baseStart_1367795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367796 : List Nat := [2, 6, 1, 1, 1, 1, 4, 7]
def baseStart_1367796 : Nat := 118140960795 + 1367796 * 2 ^ 59
def prefixEnd_1367796 : Nat := 4983230072969 + 3 ^ 40 * 1367796 * 2
def baseEnd_1367796 : Nat := 26012473529527249094801

theorem tailTrace_1367796 : CollatzResearch.WordTrace tailWord_1367796 prefixEnd_1367796 26012473529527249094801 := by
  unfold tailWord_1367796
  simp only [CollatzResearch.WordTrace]
  refine ⟨24943809276358083901993621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33258412368477445202658161 24943809276358083901993621)
  ·
    refine ⟨1169241059829285182905951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24943809276358083901993621 1169241059829285182905951)
    ·
      refine ⟨1753861589743927774358927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169241059829285182905951 1753861589743927774358927)
      ·
        refine ⟨2630792384615891661538391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753861589743927774358927 2630792384615891661538391)
        ·
          refine ⟨3946188576923837492307587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2630792384615891661538391 3946188576923837492307587)
          ·
            refine ⟨5919282865385756238461381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946188576923837492307587 5919282865385756238461381)
            ·
              refine ⟨1109865537259829294711509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5919282865385756238461381 1109865537259829294711509)
              ·
                refine ⟨26012473529527249094801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1109865537259829294711509 26012473529527249094801)
                ·
                  rfl

theorem cell23_1367796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 7].length) (baseStart_1367796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367796 prefixEnd_1367796 := by exact prefixLift 1367796
  have htrace : WordTrace (prefixWord ++ tailWord_1367796) baseStart_1367796 baseEnd_1367796 := by
    simpa [prefixWord, tailWord_1367796, baseEnd_1367796] using wordTrace_append hprefix tailTrace_1367796
  have hstable : (prefixWord ++ tailWord_1367796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367796).length < 2 ^ (prefixWord ++ tailWord_1367796).sum := by decide
  have hdescent : baseEnd_1367796 < baseStart_1367796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367799 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_1367799 : Nat := 118140960795 + 1367799 * 2 ^ 59
def prefixEnd_1367799 : Nat := 4983230072969 + 3 ^ 40 * 1367799 * 2
def baseEnd_1367799 : Nat := 702338325739199213822113

theorem tailTrace_1367799 : CollatzResearch.WordTrace tailWord_1367799 prefixEnd_1367799 702338325739199213822113 := by
  unfold tailWord_1367799
  simp only [CollatzResearch.WordTrace]
  refine ⟨49887727971705299316346451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33258485314470199544230967 49887727971705299316346451)
  ·
    refine ⟨74831591957557948974519677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49887727971705299316346451 74831591957557948974519677)
    ·
      refine ⟨28061846984084230865444879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74831591957557948974519677 28061846984084230865444879)
      ·
        refine ⟨42092770476126346298167319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28061846984084230865444879 42092770476126346298167319)
        ·
          refine ⟨63139155714189519447250979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42092770476126346298167319 63139155714189519447250979)
          ·
            refine ⟨94708733571284279170876469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63139155714189519447250979 94708733571284279170876469)
            ·
              refine ⟨8878943772307901172269669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94708733571284279170876469 8878943772307901172269669)
              ·
                refine ⟨1664801957307731469800563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8878943772307901172269669 1664801957307731469800563)
                ·
                  refine ⟨2497202935961597204700845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664801957307731469800563 2497202935961597204700845)
                  ·
                    refine ⟨936451100985598951762817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2497202935961597204700845 936451100985598951762817)
                    ·
                      refine ⟨702338325739199213822113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936451100985598951762817 702338325739199213822113)
                      ·
                        rfl

theorem cell23_1367799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_1367799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367799 prefixEnd_1367799 := by exact prefixLift 1367799
  have htrace : WordTrace (prefixWord ++ tailWord_1367799) baseStart_1367799 baseEnd_1367799 := by
    simpa [prefixWord, tailWord_1367799, baseEnd_1367799] using wordTrace_append hprefix tailTrace_1367799
  have hstable : (prefixWord ++ tailWord_1367799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367799).length < 2 ^ (prefixWord ++ tailWord_1367799).sum := by decide
  have hdescent : baseEnd_1367799 < baseStart_1367799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367805 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1367805 : Nat := 118140960795 + 1367805 * 2 ^ 59
def prefixEnd_1367805 : Nat := 4983230072969 + 3 ^ 40 * 1367805 * 2
def baseEnd_1367805 : Nat := 234113802207708730115695

theorem tailTrace_1367805 : CollatzResearch.WordTrace tailWord_1367805 prefixEnd_1367805 234113802207708730115695 := by
  unfold tailWord_1367805
  simp only [CollatzResearch.WordTrace]
  refine ⟨49887946809683562341064869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33258631206455708227376579 49887946809683562341064869)
  ·
    refine ⟨9353990026815667938949663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49887946809683562341064869 9353990026815667938949663)
    ·
      refine ⟨14030985040223501908424495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9353990026815667938949663 14030985040223501908424495)
      ·
        refine ⟨21046477560335252862636743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14030985040223501908424495 21046477560335252862636743)
        ·
          refine ⟨31569716340502879293955115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21046477560335252862636743 31569716340502879293955115)
          ·
            refine ⟨47354574510754318940932673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31569716340502879293955115 47354574510754318940932673)
            ·
              refine ⟨35515930883065739205699505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47354574510754318940932673 35515930883065739205699505)
              ·
                refine ⟨26636948162299304404274629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35515930883065739205699505 26636948162299304404274629)
                ·
                  refine ⟨4994427780431119575801493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26636948162299304404274629 4994427780431119575801493)
                  ·
                    refine ⟨234113802207708730115695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4994427780431119575801493 234113802207708730115695)
                    ·
                      rfl

theorem cell23_1367805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1367805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367805 prefixEnd_1367805 := by exact prefixLift 1367805
  have htrace : WordTrace (prefixWord ++ tailWord_1367805) baseStart_1367805 baseEnd_1367805 := by
    simpa [prefixWord, tailWord_1367805, baseEnd_1367805] using wordTrace_append hprefix tailTrace_1367805
  have hstable : (prefixWord ++ tailWord_1367805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367805).length < 2 ^ (prefixWord ++ tailWord_1367805).sum := by decide
  have hdescent : baseEnd_1367805 < baseStart_1367805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367842 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1367842 : Nat := 118140960795 + 1367842 * 2 ^ 59
def prefixEnd_1367842 : Nat := 4983230072969 + 3 ^ 40 * 1367842 * 2
def baseEnd_1367842 : Nat := 702360405407342545584415

theorem tailTrace_1367842 : CollatzResearch.WordTrace tailWord_1367842 prefixEnd_1367842 702360405407342545584415 := by
  unfold tailWord_1367842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472324077637379415040445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33259530873699678440107853 12472324077637379415040445)
  ·
    refine ⟨4677121529114017280640167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12472324077637379415040445 4677121529114017280640167)
    ·
      refine ⟨7015682293671025920960251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4677121529114017280640167 7015682293671025920960251)
      ·
        refine ⟨10523523440506538881440377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7015682293671025920960251 10523523440506538881440377)
        ·
          refine ⟨7892642580379904161080283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10523523440506538881440377 7892642580379904161080283)
          ·
            refine ⟨11838963870569856241620425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7892642580379904161080283 11838963870569856241620425)
            ·
              refine ⟨8879222902927392181215319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11838963870569856241620425 8879222902927392181215319)
              ·
                refine ⟨13318834354391088271822979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8879222902927392181215319 13318834354391088271822979)
                ·
                  refine ⟨19978251531586632407734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13318834354391088271822979 19978251531586632407734469)
                  ·
                    refine ⟨3745922162172493576450213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19978251531586632407734469 3745922162172493576450213)
                    ·
                      refine ⟨702360405407342545584415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3745922162172493576450213 702360405407342545584415)
                      ·
                        rfl

theorem cell23_1367842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1367842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367842 prefixEnd_1367842 := by exact prefixLift 1367842
  have htrace : WordTrace (prefixWord ++ tailWord_1367842) baseStart_1367842 baseEnd_1367842 := by
    simpa [prefixWord, tailWord_1367842, baseEnd_1367842] using wordTrace_append hprefix tailTrace_1367842
  have hstable : (prefixWord ++ tailWord_1367842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367842).length < 2 ^ (prefixWord ++ tailWord_1367842).sum := by decide
  have hdescent : baseEnd_1367842 < baseStart_1367842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367882 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1367882 : Nat := 118140960795 + 1367882 * 2 ^ 59
def prefixEnd_1367882 : Nat := 4983230072969 + 3 ^ 40 * 1367882 * 2
def baseEnd_1367882 : Nat := 234126981544507463028077

theorem tailTrace_1367882 : CollatzResearch.WordTrace tailWord_1367882 prefixEnd_1367882 234126981544507463028077 := by
  unfold tailWord_1367882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12472688807601151122904475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33260503486936402994411933 12472688807601151122904475)
  ·
    refine ⟨18709033211401726684356713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12472688807601151122904475 18709033211401726684356713)
    ·
      refine ⟨14031774908551295013267535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18709033211401726684356713 14031774908551295013267535)
      ·
        refine ⟨21047662362826942519901303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14031774908551295013267535 21047662362826942519901303)
        ·
          refine ⟨31571493544240413779851955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21047662362826942519901303 31571493544240413779851955)
          ·
            refine ⟨47357240316360620669777933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31571493544240413779851955 47357240316360620669777933)
            ·
              refine ⟨17758965118635232751166725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47357240316360620669777933 17758965118635232751166725)
              ·
                refine ⟨3329805959744106140843761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17758965118635232751166725 3329805959744106140843761)
                ·
                  refine ⟨2497354469808079605632821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3329805959744106140843761 2497354469808079605632821)
                  ·
                    refine ⟨234126981544507463028077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2497354469808079605632821 234126981544507463028077)
                    ·
                      rfl

theorem cell23_1367882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1367882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367882 prefixEnd_1367882 := by exact prefixLift 1367882
  have htrace : WordTrace (prefixWord ++ tailWord_1367882) baseStart_1367882 baseEnd_1367882 := by
    simpa [prefixWord, tailWord_1367882, baseEnd_1367882] using wordTrace_append hprefix tailTrace_1367882
  have hstable : (prefixWord ++ tailWord_1367882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367882).length < 2 ^ (prefixWord ++ tailWord_1367882).sum := by decide
  have hdescent : baseEnd_1367882 < baseStart_1367882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367889 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_1367889 : Nat := 118140960795 + 1367889 * 2 ^ 59
def prefixEnd_1367889 : Nat := 4983230072969 + 3 ^ 40 * 1367889 * 2
def baseEnd_1367889 : Nat := 702384538998103861696699

theorem tailTrace_1367889 : CollatzResearch.WordTrace tailWord_1367889 prefixEnd_1367889 702384538998103861696699 := by
  unfold tailWord_1367889
  simp only [CollatzResearch.WordTrace]
  refine ⟨49891010541379244687122721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33260673694252829791415147 49891010541379244687122721)
  ·
    refine ⟨37418257906034433515342041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49891010541379244687122721 37418257906034433515342041)
    ·
      refine ⟨28063693429525825136506531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37418257906034433515342041 28063693429525825136506531)
      ·
        refine ⟨42095540144288737704759797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28063693429525825136506531 42095540144288737704759797)
        ·
          refine ⟨3946456888527069159821231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42095540144288737704759797 3946456888527069159821231)
          ·
            refine ⟨5919685332790603739731847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946456888527069159821231 5919685332790603739731847)
            ·
              refine ⟨8879527999185905609597771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5919685332790603739731847 8879527999185905609597771)
              ·
                refine ⟨13319291998778858414396657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8879527999185905609597771 13319291998778858414396657)
                ·
                  refine ⟨9989468999084143810797493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13319291998778858414396657 9989468999084143810797493)
                  ·
                    refine ⟨936512718664138482262265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9989468999084143810797493 936512718664138482262265)
                    ·
                      refine ⟨702384538998103861696699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936512718664138482262265 702384538998103861696699)
                      ·
                        rfl

theorem cell23_1367889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_1367889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367889 prefixEnd_1367889 := by exact prefixLift 1367889
  have htrace : WordTrace (prefixWord ++ tailWord_1367889) baseStart_1367889 baseEnd_1367889 := by
    simpa [prefixWord, tailWord_1367889, baseEnd_1367889] using wordTrace_append hprefix tailTrace_1367889
  have hstable : (prefixWord ++ tailWord_1367889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367889).length < 2 ^ (prefixWord ++ tailWord_1367889).sum := by decide
  have hdescent : baseEnd_1367889 < baseStart_1367889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1367952 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_1367952 : Nat := 118140960795 + 1367952 * 2 ^ 59
def prefixEnd_1367952 : Nat := 4983230072969 + 3 ^ 40 * 1367952 * 2
def baseEnd_1367952 : Nat := 702416888279337115208909

theorem tailTrace_1367952 : CollatzResearch.WordTrace tailWord_1367952 prefixEnd_1367952 702416888279337115208909 := by
  unfold tailWord_1367952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24946654170075503223333055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33262205560100670964444073 24946654170075503223333055)
  ·
    refine ⟨37419981255113254834999583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24946654170075503223333055 37419981255113254834999583)
    ·
      refine ⟨56129971882669882252499375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37419981255113254834999583 56129971882669882252499375)
      ·
        refine ⟨84194957824004823378749063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56129971882669882252499375 84194957824004823378749063)
        ·
          refine ⟨126292436736007235068123595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84194957824004823378749063 126292436736007235068123595)
          ·
            refine ⟨189438655104010852602185393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126292436736007235068123595 189438655104010852602185393)
            ·
              refine ⟨142078991328008139451639045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189438655104010852602185393 142078991328008139451639045)
              ·
                refine ⟨26639810874001526147182321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142078991328008139451639045 26639810874001526147182321)
                ·
                  refine ⟨19979858155501144610386741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26639810874001526147182321 19979858155501144610386741)
                  ·
                    refine ⟨1873111702078232307223757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19979858155501144610386741 1873111702078232307223757)
                    ·
                      refine ⟨702416888279337115208909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873111702078232307223757 702416888279337115208909)
                      ·
                        rfl

theorem cell23_1367952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_1367952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1367952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1367952 prefixEnd_1367952 := by exact prefixLift 1367952
  have htrace : WordTrace (prefixWord ++ tailWord_1367952) baseStart_1367952 baseEnd_1367952 := by
    simpa [prefixWord, tailWord_1367952, baseEnd_1367952] using wordTrace_append hprefix tailTrace_1367952
  have hstable : (prefixWord ++ tailWord_1367952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1367952).length < 2 ^ (prefixWord ++ tailWord_1367952).sum := by decide
  have hdescent : baseEnd_1367952 < baseStart_1367952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1367952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368026 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_1368026 : Nat := 118140960795 + 1368026 * 2 ^ 59
def prefixEnd_1368026 : Nat := 4983230072969 + 3 ^ 40 * 1368026 * 2
def baseEnd_1368026 : Nat := 702454885847769825683569

theorem tailTrace_1368026 : CollatzResearch.WordTrace tailWord_1368026 prefixEnd_1368026 702454885847769825683569 := by
  unfold tailWord_1368026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474001835470729271214983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33264004894588611389906621 12474001835470729271214983)
  ·
    refine ⟨18711002753206093906822475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12474001835470729271214983 18711002753206093906822475)
    ·
      refine ⟨28066504129809140860233713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18711002753206093906822475 28066504129809140860233713)
      ·
        refine ⟨21049878097356855645175285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28066504129809140860233713 21049878097356855645175285)
        ·
          refine ⟨1973426071627205216735183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21049878097356855645175285 1973426071627205216735183)
          ·
            refine ⟨2960139107440807825102775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973426071627205216735183 2960139107440807825102775)
            ·
              refine ⟨4440208661161211737654163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2960139107440807825102775 4440208661161211737654163)
              ·
                refine ⟨6660312991741817606481245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4440208661161211737654163 6660312991741817606481245)
                ·
                  refine ⟨2497617371903181602430467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6660312991741817606481245 2497617371903181602430467)
                  ·
                    refine ⟨3746426057854772403645701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497617371903181602430467 3746426057854772403645701)
                    ·
                      refine ⟨702454885847769825683569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3746426057854772403645701 702454885847769825683569)
                      ·
                        rfl

theorem cell23_1368026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_1368026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368026 prefixEnd_1368026 := by exact prefixLift 1368026
  have htrace : WordTrace (prefixWord ++ tailWord_1368026) baseStart_1368026 baseEnd_1368026 := by
    simpa [prefixWord, tailWord_1368026, baseEnd_1368026] using wordTrace_append hprefix tailTrace_1368026
  have hstable : (prefixWord ++ tailWord_1368026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368026).length < 2 ^ (prefixWord ++ tailWord_1368026).sum := by decide
  have hdescent : baseEnd_1368026 < baseStart_1368026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368046 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1368046 : Nat := 118140960795 + 1368046 * 2 ^ 59
def prefixEnd_1368046 : Nat := 4983230072969 + 3 ^ 40 * 1368046 * 2
def baseEnd_1368046 : Nat := 702465155460859747433477

theorem tailTrace_1368046 : CollatzResearch.WordTrace tailWord_1368046 prefixEnd_1368046 702465155460859747433477 := by
  unfold tailWord_1368046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237092100226307562573499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33264491201206973667058661 6237092100226307562573499)
  ·
    refine ⟨9355638150339461343860249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6237092100226307562573499 9355638150339461343860249)
    ·
      refine ⟨7016728612754596007895187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9355638150339461343860249 7016728612754596007895187)
      ·
        refine ⟨10525092919131894011842781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7016728612754596007895187 10525092919131894011842781)
        ·
          refine ⟨3946909844674460254441043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10525092919131894011842781 3946909844674460254441043)
          ·
            refine ⟨5920364767011690381661565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3946909844674460254441043 5920364767011690381661565)
            ·
              refine ⟨2220136787629383893123087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5920364767011690381661565 2220136787629383893123087)
              ·
                refine ⟨3330205181444075839684631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220136787629383893123087 3330205181444075839684631)
                ·
                  refine ⟨4995307772166113759526947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330205181444075839684631 4995307772166113759526947)
                  ·
                    refine ⟨7492961658249170639290421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4995307772166113759526947 7492961658249170639290421)
                    ·
                      refine ⟨702465155460859747433477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7492961658249170639290421 702465155460859747433477)
                      ·
                        rfl

theorem cell23_1368046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1368046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368046 prefixEnd_1368046 := by exact prefixLift 1368046
  have htrace : WordTrace (prefixWord ++ tailWord_1368046) baseStart_1368046 baseEnd_1368046 := by
    simpa [prefixWord, tailWord_1368046, baseEnd_1368046] using wordTrace_append hprefix tailTrace_1368046
  have hstable : (prefixWord ++ tailWord_1368046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368046).length < 2 ^ (prefixWord ++ tailWord_1368046).sum := by decide
  have hdescent : baseEnd_1368046 < baseStart_1368046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368049 : List Nat := [1, 2, 2, 2, 6, 10]
def baseStart_1368049 : Nat := 118140960795 + 1368049 * 2 ^ 59
def prefixEnd_1368049 : Nat := 4983230072969 + 3 ^ 40 * 1368049 * 2
def baseEnd_1368049 : Nat := 2890809448159766402041

theorem tailTrace_1368049 : CollatzResearch.WordTrace tailWord_1368049 prefixEnd_1368049 2890809448159766402041 := by
  unfold tailWord_1368049
  simp only [CollatzResearch.WordTrace]
  refine ⟨49896846220799592012947201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33264564147199728008631467 49896846220799592012947201)
  ·
    refine ⟨37422634665599694009710401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49896846220799592012947201 37422634665599694009710401)
    ·
      refine ⟨28066975999199770507282801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37422634665599694009710401 28066975999199770507282801)
      ·
        refine ⟨21050231999399827880462101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28066975999199770507282801 21050231999399827880462101)
        ·
          refine ⟨986729624971866931896661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21050231999399827880462101 986729624971866931896661)
          ·
            refine ⟨2890809448159766402041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 986729624971866931896661 2890809448159766402041)
            ·
              rfl

theorem cell23_1368049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 10].length) (baseStart_1368049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368049 prefixEnd_1368049 := by exact prefixLift 1368049
  have htrace : WordTrace (prefixWord ++ tailWord_1368049) baseStart_1368049 baseEnd_1368049 := by
    simpa [prefixWord, tailWord_1368049, baseEnd_1368049] using wordTrace_append hprefix tailTrace_1368049
  have hstable : (prefixWord ++ tailWord_1368049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368049).length < 2 ^ (prefixWord ++ tailWord_1368049).sum := by decide
  have hdescent : baseEnd_1368049 < baseStart_1368049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368054 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1368054 : Nat := 118140960795 + 1368054 * 2 ^ 59
def prefixEnd_1368054 : Nat := 4983230072969 + 3 ^ 40 * 1368054 * 2
def baseEnd_1368054 : Nat := 702469263306095716133441

theorem tailTrace_1368054 : CollatzResearch.WordTrace tailWord_1368054 prefixEnd_1368054 702469263306095716133441 := by
  unfold tailWord_1368054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118564286611342366679951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33264685723854318577919477 3118564286611342366679951)
  ·
    refine ⟨4677846429917013550019927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3118564286611342366679951 4677846429917013550019927)
    ·
      refine ⟨7016769644875520325029891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4677846429917013550019927 7016769644875520325029891)
      ·
        refine ⟨10525154467313280487544837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7016769644875520325029891 10525154467313280487544837)
        ·
          refine ⟨1973466462621240091414657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10525154467313280487544837 1973466462621240091414657)
          ·
            refine ⟨1480099846965930068560993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973466462621240091414657 1480099846965930068560993)
            ·
              refine ⟨1110074885224447551420745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480099846965930068560993 1110074885224447551420745)
              ·
                refine ⟨832556163918335663565559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110074885224447551420745 832556163918335663565559)
                ·
                  refine ⟨1248834245877503495348339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832556163918335663565559 1248834245877503495348339)
                  ·
                    refine ⟨1873251368816255243022509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248834245877503495348339 1873251368816255243022509)
                    ·
                      refine ⟨702469263306095716133441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873251368816255243022509 702469263306095716133441)
                      ·
                        rfl

theorem cell23_1368054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1368054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368054 prefixEnd_1368054 := by exact prefixLift 1368054
  have htrace : WordTrace (prefixWord ++ tailWord_1368054) baseStart_1368054 baseEnd_1368054 := by
    simpa [prefixWord, tailWord_1368054, baseEnd_1368054] using wordTrace_append hprefix tailTrace_1368054
  have hstable : (prefixWord ++ tailWord_1368054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368054).length < 2 ^ (prefixWord ++ tailWord_1368054).sum := by decide
  have hdescent : baseEnd_1368054 < baseStart_1368054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368060 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_1368060 : Nat := 118140960795 + 1368060 * 2 ^ 59
def prefixEnd_1368060 : Nat := 4983230072969 + 3 ^ 40 * 1368060 * 2
def baseEnd_1368060 : Nat := 702472344190022692658413

theorem tailTrace_1368060 : CollatzResearch.WordTrace tailWord_1368060 prefixEnd_1368060 702472344190022692658413 := by
  unfold tailWord_1368060
  simp only [CollatzResearch.WordTrace]
  refine ⟨24948623711879870445798817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33264831615839827261065089 24948623711879870445798817)
  ·
    refine ⟨18711467783909902834349113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24948623711879870445798817 18711467783909902834349113)
    ·
      refine ⟨14033600837932427125761835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18711467783909902834349113 14033600837932427125761835)
      ·
        refine ⟨21050401256898640688642753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14033600837932427125761835 21050401256898640688642753)
        ·
          refine ⟨15787800942673980516482065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21050401256898640688642753 15787800942673980516482065)
          ·
            refine ⟨11840850707005485387361549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15787800942673980516482065 11840850707005485387361549)
            ·
              refine ⟨4440319015127057020260581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11840850707005485387361549 4440319015127057020260581)
              ·
                refine ⟨832559815336323191298859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4440319015127057020260581 832559815336323191298859)
                ·
                  refine ⟨1248839723004484786948289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832559815336323191298859 1248839723004484786948289)
                  ·
                    refine ⟨936629792253363590211217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1248839723004484786948289 936629792253363590211217)
                    ·
                      refine ⟨702472344190022692658413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936629792253363590211217 702472344190022692658413)
                      ·
                        rfl

theorem cell23_1368060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_1368060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368060 prefixEnd_1368060 := by exact prefixLift 1368060
  have htrace : WordTrace (prefixWord ++ tailWord_1368060) baseStart_1368060 baseEnd_1368060 := by
    simpa [prefixWord, tailWord_1368060, baseEnd_1368060] using wordTrace_append hprefix tailTrace_1368060
  have hstable : (prefixWord ++ tailWord_1368060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368060).length < 2 ^ (prefixWord ++ tailWord_1368060).sum := by decide
  have hdescent : baseEnd_1368060 < baseStart_1368060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368076 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1368076 : Nat := 118140960795 + 1368076 * 2 ^ 59
def prefixEnd_1368076 : Nat := 4983230072969 + 3 ^ 40 * 1368076 * 2
def baseEnd_1368076 : Nat := 702480559880494630058339

theorem tailTrace_1368076 : CollatzResearch.WordTrace tailWord_1368076 prefixEnd_1368076 702480559880494630058339 := by
  unfold tailWord_1368076
  simp only [CollatzResearch.WordTrace]
  refine ⟨24948915495850887812090041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33265220661134517082786721 24948915495850887812090041)
  ·
    refine ⟨18711686621888165859067531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24948915495850887812090041 18711686621888165859067531)
    ·
      refine ⟨28067529932832248788601297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18711686621888165859067531 28067529932832248788601297)
      ·
        refine ⟨21050647449624186591450973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28067529932832248788601297 21050647449624186591450973)
        ·
          refine ⟨7893992793609069971794115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21050647449624186591450973 7893992793609069971794115)
          ·
            refine ⟨11840989190413604957691173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7893992793609069971794115 11840989190413604957691173)
            ·
              refine ⟨2220185473202550929567095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11840989190413604957691173 2220185473202550929567095)
              ·
                refine ⟨3330278209803826394350643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220185473202550929567095 3330278209803826394350643)
                ·
                  refine ⟨4995417314705739591525965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3330278209803826394350643 4995417314705739591525965)
                  ·
                    refine ⟨1873281493014652346822237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4995417314705739591525965 1873281493014652346822237)
                    ·
                      refine ⟨702480559880494630058339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873281493014652346822237 702480559880494630058339)
                      ·
                        rfl

theorem cell23_1368076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1368076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368076 prefixEnd_1368076 := by exact prefixLift 1368076
  have htrace : WordTrace (prefixWord ++ tailWord_1368076) baseStart_1368076 baseEnd_1368076 := by
    simpa [prefixWord, tailWord_1368076, baseEnd_1368076] using wordTrace_append hprefix tailTrace_1368076
  have hstable : (prefixWord ++ tailWord_1368076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368076).length < 2 ^ (prefixWord ++ tailWord_1368076).sum := by decide
  have hdescent : baseEnd_1368076 < baseStart_1368076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368097 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_1368097 : Nat := 118140960795 + 1368097 * 2 ^ 59
def prefixEnd_1368097 : Nat := 4983230072969 + 3 ^ 40 * 1368097 * 2
def baseEnd_1368097 : Nat := 702491342974239047895743

theorem tailTrace_1368097 : CollatzResearch.WordTrace tailWord_1368097 prefixEnd_1368097 702491342974239047895743 := by
  unfold tailWord_1368097
  simp only [CollatzResearch.WordTrace]
  refine ⟨49898596924625696210694545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33265731283083797473796363 49898596924625696210694545)
  ·
    refine ⟨37423947693469272158020909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49898596924625696210694545 37423947693469272158020909)
    ·
      refine ⟨14033980385050977059257841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37423947693469272158020909 14033980385050977059257841)
      ·
        refine ⟨10525485288788232794443381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14033980385050977059257841 10525485288788232794443381)
        ·
          refine ⟨986764245823896824479067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10525485288788232794443381 986764245823896824479067)
          ·
            refine ⟨1480146368735845236718601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986764245823896824479067 1480146368735845236718601)
            ·
              refine ⟨1110109776551883927538951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480146368735845236718601 1110109776551883927538951)
              ·
                refine ⟨1665164664827825891308427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110109776551883927538951 1665164664827825891308427)
                ·
                  refine ⟨2497746997241738836962641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665164664827825891308427 2497746997241738836962641)
                  ·
                    refine ⟨1873310247931304127721981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2497746997241738836962641 1873310247931304127721981)
                    ·
                      refine ⟨702491342974239047895743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873310247931304127721981 702491342974239047895743)
                      ·
                        rfl

theorem cell23_1368097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_1368097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368097 prefixEnd_1368097 := by exact prefixLift 1368097
  have htrace : WordTrace (prefixWord ++ tailWord_1368097) baseStart_1368097 baseEnd_1368097 := by
    simpa [prefixWord, tailWord_1368097, baseEnd_1368097] using wordTrace_append hprefix tailTrace_1368097
  have hstable : (prefixWord ++ tailWord_1368097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368097).length < 2 ^ (prefixWord ++ tailWord_1368097).sum := by decide
  have hdescent : baseEnd_1368097 < baseStart_1368097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368110 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1368110 : Nat := 118140960795 + 1368110 * 2 ^ 59
def prefixEnd_1368110 : Nat := 4983230072969 + 3 ^ 40 * 1368110 * 2
def baseEnd_1368110 : Nat := 702498018222747497033183

theorem tailTrace_1368110 : CollatzResearch.WordTrace tailWord_1368110 prefixEnd_1368110 702498018222747497033183 := by
  unfold tailWord_1368110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237383884197324928864723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33266047382385732953945189 6237383884197324928864723)
  ·
    refine ⟨9356075826295987393297085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6237383884197324928864723 9356075826295987393297085)
    ·
      refine ⟨3508528434860995272486407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9356075826295987393297085 3508528434860995272486407)
      ·
        refine ⟨5262792652291492908729611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508528434860995272486407 5262792652291492908729611)
        ·
          refine ⟨7894188978437239363094417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262792652291492908729611 7894188978437239363094417)
          ·
            refine ⟨5920641733827929522320813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7894188978437239363094417 5920641733827929522320813)
            ·
              refine ⟨2220240650185473570870305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5920641733827929522320813 2220240650185473570870305)
              ·
                refine ⟨1665180487639105178152729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2220240650185473570870305 1665180487639105178152729)
                ·
                  refine ⟨1248885365729328883614547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1665180487639105178152729 1248885365729328883614547)
                  ·
                    refine ⟨1873328048593993325421821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248885365729328883614547 1873328048593993325421821)
                    ·
                      refine ⟨702498018222747497033183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873328048593993325421821 702498018222747497033183)
                      ·
                        rfl

theorem cell23_1368110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1368110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368110 prefixEnd_1368110 := by exact prefixLift 1368110
  have htrace : WordTrace (prefixWord ++ tailWord_1368110) baseStart_1368110 baseEnd_1368110 := by
    simpa [prefixWord, tailWord_1368110, baseEnd_1368110] using wordTrace_append hprefix tailTrace_1368110
  have hstable : (prefixWord ++ tailWord_1368110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368110).length < 2 ^ (prefixWord ++ tailWord_1368110).sum := by decide
  have hdescent : baseEnd_1368110 < baseStart_1368110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368119 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_1368119 : Nat := 118140960795 + 1368119 * 2 ^ 59
def prefixEnd_1368119 : Nat := 4983230072969 + 3 ^ 40 * 1368119 * 2
def baseEnd_1368119 : Nat := 702502639548637961820641

theorem tailTrace_1368119 : CollatzResearch.WordTrace tailWord_1368119 prefixEnd_1368119 702502639548637961820641 := by
  unfold tailWord_1368119
  simp only [CollatzResearch.WordTrace]
  refine ⟨49899399330545993967995411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33266266220363995978663607 49899399330545993967995411)
  ·
    refine ⟨74849098995818990951993117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49899399330545993967995411 74849098995818990951993117)
    ·
      refine ⟨28068412123432121606997419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74849098995818990951993117 28068412123432121606997419)
      ·
        refine ⟨42102618185148182410496129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28068412123432121606997419 42102618185148182410496129)
        ·
          refine ⟨31576963638861136807872097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42102618185148182410496129 31576963638861136807872097)
          ·
            refine ⟨23682722729145852605904073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31576963638861136807872097 23682722729145852605904073)
            ·
              refine ⟨17762042046859389454428055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23682722729145852605904073 17762042046859389454428055)
              ·
                refine ⟨26643063070289084181642083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17762042046859389454428055 26643063070289084181642083)
                ·
                  refine ⟨39964594605433626272463125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26643063070289084181642083 39964594605433626272463125)
                  ·
                    refine ⟨1873340372129701231521709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39964594605433626272463125 1873340372129701231521709)
                    ·
                      refine ⟨702502639548637961820641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873340372129701231521709 702502639548637961820641)
                      ·
                        rfl

theorem cell23_1368119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_1368119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368119 prefixEnd_1368119 := by exact prefixLift 1368119
  have htrace : WordTrace (prefixWord ++ tailWord_1368119) baseStart_1368119 baseEnd_1368119 := by
    simpa [prefixWord, tailWord_1368119, baseEnd_1368119] using wordTrace_append hprefix tailTrace_1368119
  have hstable : (prefixWord ++ tailWord_1368119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368119).length < 2 ^ (prefixWord ++ tailWord_1368119).sum := by decide
  have hdescent : baseEnd_1368119 < baseStart_1368119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368199 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 8]
def baseStart_1368199 : Nat := 118140960795 + 1368199 * 2 ^ 59
def prefixEnd_1368199 : Nat := 4983230072969 + 3 ^ 40 * 1368199 * 2
def baseEnd_1368199 : Nat := 234181239333665882940091

theorem tailTrace_1368199 : CollatzResearch.WordTrace tailWord_1368199 prefixEnd_1368199 234181239333665882940091 := by
  unfold tailWord_1368199
  simp only [CollatzResearch.WordTrace]
  refine ⟨49902317170256167630907651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33268211446837445087271767 49902317170256167630907651)
  ·
    refine ⟨74853475755384251446361477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49902317170256167630907651 74853475755384251446361477)
    ·
      refine ⟨14035026704134547146192777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74853475755384251446361477 14035026704134547146192777)
      ·
        refine ⟨10526270028100910359644583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14035026704134547146192777 10526270028100910359644583)
        ·
          refine ⟨15789405042151365539466875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10526270028100910359644583 15789405042151365539466875)
          ·
            refine ⟨23684107563227048309200313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15789405042151365539466875 23684107563227048309200313)
            ·
              refine ⟨17763080672420286231900235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23684107563227048309200313 17763080672420286231900235)
              ·
                refine ⟨26644621008630429347850353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17763080672420286231900235 26644621008630429347850353)
                ·
                  refine ⟨19983465756472822010887765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26644621008630429347850353 19983465756472822010887765)
                  ·
                    refine ⟨234181239333665882940091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19983465756472822010887765 234181239333665882940091)
                    ·
                      rfl

theorem cell23_1368199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_1368199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368199 prefixEnd_1368199 := by exact prefixLift 1368199
  have htrace : WordTrace (prefixWord ++ tailWord_1368199) baseStart_1368199 baseEnd_1368199 := by
    simpa [prefixWord, tailWord_1368199, baseEnd_1368199] using wordTrace_append hprefix tailTrace_1368199
  have hstable : (prefixWord ++ tailWord_1368199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368199).length < 2 ^ (prefixWord ++ tailWord_1368199).sum := by decide
  have hdescent : baseEnd_1368199 < baseStart_1368199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368219 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4]
def baseStart_1368219 : Nat := 118140960795 + 1368219 * 2 ^ 59
def prefixEnd_1368219 : Nat := 4983230072969 + 3 ^ 40 * 1368219 * 2
def baseEnd_1368219 : Nat := 702553987614087570570181

theorem tailTrace_1368219 : CollatzResearch.WordTrace tailWord_1368219 prefixEnd_1368219 702553987614087570570181 := by
  unfold tailWord_1368219
  simp only [CollatzResearch.WordTrace]
  refine ⟨49903046630183711046635711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33268697753455807364423807 49903046630183711046635711)
  ·
    refine ⟨74854569945275566569953567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49903046630183711046635711 74854569945275566569953567)
    ·
      refine ⟨112281854917913349854930351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74854569945275566569953567 112281854917913349854930351)
      ·
        refine ⟨168422782376870024782395527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112281854917913349854930351 168422782376870024782395527)
        ·
          refine ⟨252634173565305037173593291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168422782376870024782395527 252634173565305037173593291)
          ·
            refine ⟨378951260347957555760389937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252634173565305037173593291 378951260347957555760389937)
            ·
              refine ⟨284213445260968166820292453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378951260347957555760389937 284213445260968166820292453)
              ·
                refine ⟨53290020986431531278804835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284213445260968166820292453 53290020986431531278804835)
                ·
                  refine ⟨79935031479647296918207253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53290020986431531278804835 79935031479647296918207253)
                  ·
                    refine ⟨3746954600608467043040965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79935031479647296918207253 3746954600608467043040965)
                    ·
                      refine ⟨702553987614087570570181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3746954600608467043040965 702553987614087570570181)
                      ·
                        rfl

theorem cell23_1368219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 4].length) (baseStart_1368219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368219 prefixEnd_1368219 := by exact prefixLift 1368219
  have htrace : WordTrace (prefixWord ++ tailWord_1368219) baseStart_1368219 baseEnd_1368219 := by
    simpa [prefixWord, tailWord_1368219, baseEnd_1368219] using wordTrace_append hprefix tailTrace_1368219
  have hstable : (prefixWord ++ tailWord_1368219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368219).length < 2 ^ (prefixWord ++ tailWord_1368219).sum := by decide
  have hdescent : baseEnd_1368219 < baseStart_1368219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368223 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1368223 : Nat := 118140960795 + 1368223 * 2 ^ 59
def prefixEnd_1368223 : Nat := 4983230072969 + 3 ^ 40 * 1368223 * 2
def baseEnd_1368223 : Nat := 702556041536705554920163

theorem tailTrace_1368223 : CollatzResearch.WordTrace tailWord_1368223 prefixEnd_1368223 702556041536705554920163 := by
  unfold tailWord_1368223
  simp only [CollatzResearch.WordTrace]
  refine ⟨49903192522169219729781323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33268795014779479819854215 49903192522169219729781323)
  ·
    refine ⟨74854788783253829594671985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49903192522169219729781323 74854788783253829594671985)
    ·
      refine ⟨56141091587440372196003989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74854788783253829594671985 56141091587440372196003989)
      ·
        refine ⟨2631613668161267446687687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 56141091587440372196003989 2631613668161267446687687)
        ·
          refine ⟨3947420502241901170031531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631613668161267446687687 3947420502241901170031531)
          ·
            refine ⟨5921130753362851755047297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947420502241901170031531 5921130753362851755047297)
            ·
              refine ⟨4440848065022138816285473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5921130753362851755047297 4440848065022138816285473)
              ·
                refine ⟨3330636048766604112214105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4440848065022138816285473 3330636048766604112214105)
                ·
                  refine ⟨2497977036574953084160579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330636048766604112214105 2497977036574953084160579)
                  ·
                    refine ⟨3746965554862429626240869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2497977036574953084160579 3746965554862429626240869)
                    ·
                      refine ⟨702556041536705554920163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3746965554862429626240869 702556041536705554920163)
                      ·
                        rfl

theorem cell23_1368223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1368223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368223 prefixEnd_1368223 := by exact prefixLift 1368223
  have htrace : WordTrace (prefixWord ++ tailWord_1368223) baseStart_1368223 baseEnd_1368223 := by
    simpa [prefixWord, tailWord_1368223, baseEnd_1368223] using wordTrace_append hprefix tailTrace_1368223
  have hstable : (prefixWord ++ tailWord_1368223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368223).length < 2 ^ (prefixWord ++ tailWord_1368223).sum := by decide
  have hdescent : baseEnd_1368223 < baseStart_1368223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368257 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1368257 : Nat := 118140960795 + 1368257 * 2 ^ 59
def prefixEnd_1368257 : Nat := 4983230072969 + 3 ^ 40 * 1368257 * 2
def baseEnd_1368257 : Nat := 702573499878958421895007

theorem tailTrace_1368257 : CollatzResearch.WordTrace tailWord_1368257 prefixEnd_1368257 702573499878958421895007 := by
  unfold tailWord_1368257
  simp only [CollatzResearch.WordTrace]
  refine ⟨49904432604046043536519025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33269621736030695691012683 49904432604046043536519025)
  ·
    refine ⟨37428324453034532652389269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49904432604046043536519025 37428324453034532652389269)
    ·
      refine ⟨1754452708735993718080747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37428324453034532652389269 1754452708735993718080747)
      ·
        refine ⟨2631679063103990577121121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754452708735993718080747 2631679063103990577121121)
        ·
          refine ⟨1973759297327992932840841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631679063103990577121121 1973759297327992932840841)
          ·
            refine ⟨1480319472995994699630631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973759297327992932840841 1480319472995994699630631)
            ·
              refine ⟨2220479209493992049445947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480319472995994699630631 2220479209493992049445947)
              ·
                refine ⟨3330718814240988074168921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220479209493992049445947 3330718814240988074168921)
                ·
                  refine ⟨2498039110680741055626691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330718814240988074168921 2498039110680741055626691)
                  ·
                    refine ⟨3747058666021111583440037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2498039110680741055626691 3747058666021111583440037)
                    ·
                      refine ⟨702573499878958421895007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3747058666021111583440037 702573499878958421895007)
                      ·
                        rfl

theorem cell23_1368257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1368257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368257 prefixEnd_1368257 := by exact prefixLift 1368257
  have htrace : WordTrace (prefixWord ++ tailWord_1368257) baseStart_1368257 baseEnd_1368257 := by
    simpa [prefixWord, tailWord_1368257, baseEnd_1368257] using wordTrace_append hprefix tailTrace_1368257
  have hstable : (prefixWord ++ tailWord_1368257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368257).length < 2 ^ (prefixWord ++ tailWord_1368257).sum := by decide
  have hdescent : baseEnd_1368257 < baseStart_1368257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368260 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1368260 : Nat := 118140960795 + 1368260 * 2 ^ 59
def prefixEnd_1368260 : Nat := 4983230072969 + 3 ^ 40 * 1368260 * 2
def baseEnd_1368260 : Nat := 702575040320921910157493

theorem tailTrace_1368260 : CollatzResearch.WordTrace tailWord_1368260 prefixEnd_1368260 702575040320921910157493 := by
  unfold tailWord_1368260
  simp only [CollatzResearch.WordTrace]
  refine ⟨24952271011517587524439117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33269694682023450032585489 24952271011517587524439117)
  ·
    refine ⟨9357101629319095321664669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24952271011517587524439117 9357101629319095321664669)
    ·
      refine ⟨3508913110994660745624251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9357101629319095321664669 3508913110994660745624251)
      ·
        refine ⟨5263369666491991118436377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3508913110994660745624251 5263369666491991118436377)
        ·
          refine ⟨3947527249868993338827283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5263369666491991118436377 3947527249868993338827283)
          ·
            refine ⟨5921290874803490008240925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3947527249868993338827283 5921290874803490008240925)
            ·
              refine ⟨2220484078051308753090347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5921290874803490008240925 2220484078051308753090347)
              ·
                refine ⟨3330726117076963129635521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220484078051308753090347 3330726117076963129635521)
                ·
                  refine ⟨2498044587807722347226641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3330726117076963129635521 2498044587807722347226641)
                  ·
                    refine ⟨1873533440855791760419981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2498044587807722347226641 1873533440855791760419981)
                    ·
                      refine ⟨702575040320921910157493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1873533440855791760419981 702575040320921910157493)
                      ·
                        rfl

theorem cell23_1368260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1368260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368260 prefixEnd_1368260 := by exact prefixLift 1368260
  have htrace : WordTrace (prefixWord ++ tailWord_1368260) baseStart_1368260 baseEnd_1368260 := by
    simpa [prefixWord, tailWord_1368260, baseEnd_1368260] using wordTrace_append hprefix tailTrace_1368260
  have hstable : (prefixWord ++ tailWord_1368260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368260).length < 2 ^ (prefixWord ++ tailWord_1368260).sum := by decide
  have hdescent : baseEnd_1368260 < baseStart_1368260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368330 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_1368330 : Nat := 118140960795 + 1368330 * 2 ^ 59
def prefixEnd_1368330 : Nat := 4983230072969 + 3 ^ 40 * 1368330 * 2
def baseEnd_1368330 : Nat := 702610983966736636282171

theorem tailTrace_1368330 : CollatzResearch.WordTrace tailWord_1368330 prefixEnd_1368330 702610983966736636282171 := by
  unfold tailWord_1368330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476773783195394250981611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33271396755187718002617629 12476773783195394250981611)
  ·
    refine ⟨18715160674793091376472417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12476773783195394250981611 18715160674793091376472417)
    ·
      refine ⟨14036370506094818532354313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18715160674793091376472417 14036370506094818532354313)
      ·
        refine ⟨10527277879571113899265735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14036370506094818532354313 10527277879571113899265735)
        ·
          refine ⟨15790916819356670848898603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527277879571113899265735 15790916819356670848898603)
          ·
            refine ⟨23686375229035006273347905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15790916819356670848898603 23686375229035006273347905)
            ·
              refine ⟨17764781421776254705010929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23686375229035006273347905 17764781421776254705010929)
              ·
                refine ⟨13323586066332191028758197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17764781421776254705010929 13323586066332191028758197)
                ·
                  refine ⟨1249086193718642908946081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13323586066332191028758197 1249086193718642908946081)
                  ·
                    refine ⟨936814645288982181709561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1249086193718642908946081 936814645288982181709561)
                    ·
                      refine ⟨702610983966736636282171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936814645288982181709561 702610983966736636282171)
                      ·
                        rfl

theorem cell23_1368330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_1368330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368330 prefixEnd_1368330 := by exact prefixLift 1368330
  have htrace : WordTrace (prefixWord ++ tailWord_1368330) baseStart_1368330 baseEnd_1368330 := by
    simpa [prefixWord, tailWord_1368330, baseEnd_1368330] using wordTrace_append hprefix tailTrace_1368330
  have hstable : (prefixWord ++ tailWord_1368330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368330).length < 2 ^ (prefixWord ++ tailWord_1368330).sum := by decide
  have hdescent : baseEnd_1368330 < baseStart_1368330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368347 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 1, 2, 2]
def baseStart_1368347 : Nat := 118140960795 + 1368347 * 2 ^ 59
def prefixEnd_1368347 : Nat := 4983230072969 + 3 ^ 40 * 1368347 * 2
def baseEnd_1368347 : Nat := 702619713137863069769593

theorem tailTrace_1368347 : CollatzResearch.WordTrace tailWord_1368347 prefixEnd_1368347 702619713137863069769593 := by
  unfold tailWord_1368347
  simp only [CollatzResearch.WordTrace]
  refine ⟨49907715173719988907295295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33271810115813325938196863 49907715173719988907295295)
  ·
    refine ⟨74861572760579983360942943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49907715173719988907295295 74861572760579983360942943)
    ·
      refine ⟨112292359140869975041414415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74861572760579983360942943 112292359140869975041414415)
      ·
        refine ⟨168438538711304962562121623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112292359140869975041414415 168438538711304962562121623)
        ·
          refine ⟨252657808066957443843182435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168438538711304962562121623 252657808066957443843182435)
          ·
            refine ⟨378986712100436165764773653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252657808066957443843182435 378986712100436165764773653)
            ·
              refine ⟨17765002129707945270223765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 378986712100436165764773653 17765002129707945270223765)
              ·
                refine ⟨832734474830059934541739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17765002129707945270223765 832734474830059934541739)
                ·
                  refine ⟨1249101712245089901812609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832734474830059934541739 1249101712245089901812609)
                  ·
                    refine ⟨936826284183817426359457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1249101712245089901812609 936826284183817426359457)
                    ·
                      refine ⟨702619713137863069769593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936826284183817426359457 702619713137863069769593)
                      ·
                        rfl

theorem cell23_1368347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 1, 2, 2].length) (baseStart_1368347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368347 prefixEnd_1368347 := by exact prefixLift 1368347
  have htrace : WordTrace (prefixWord ++ tailWord_1368347) baseStart_1368347 baseEnd_1368347 := by
    simpa [prefixWord, tailWord_1368347, baseEnd_1368347] using wordTrace_append hprefix tailTrace_1368347
  have hstable : (prefixWord ++ tailWord_1368347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368347).length < 2 ^ (prefixWord ++ tailWord_1368347).sum := by decide
  have hdescent : baseEnd_1368347 < baseStart_1368347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368376 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1368376 : Nat := 118140960795 + 1368376 * 2 ^ 59
def prefixEnd_1368376 : Nat := 4983230072969 + 3 ^ 40 * 1368376 * 2
def baseEnd_1368376 : Nat := 702634604076843456306959

theorem tailTrace_1368376 : CollatzResearch.WordTrace tailWord_1368376 prefixEnd_1368376 702634604076843456306959 := by
  unfold tailWord_1368376
  simp only [CollatzResearch.WordTrace]
  refine ⟨24954386445307463430050491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33272515260409951240067321 24954386445307463430050491)
  ·
    refine ⟨37431579667961195145075737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24954386445307463430050491 37431579667961195145075737)
    ·
      refine ⟨28073684750970896358806803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37431579667961195145075737 28073684750970896358806803)
      ·
        refine ⟨42110527126456344538210205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28073684750970896358806803 42110527126456344538210205)
        ·
          refine ⟨15791447672421129201828827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42110527126456344538210205 15791447672421129201828827)
          ·
            refine ⟨23687171508631693802743241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15791447672421129201828827 23687171508631693802743241)
            ·
              refine ⟨17765378631473770352057431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23687171508631693802743241 17765378631473770352057431)
              ·
                refine ⟨26648067947210655528086147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17765378631473770352057431 26648067947210655528086147)
                ·
                  refine ⟨39972101920815983292129221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26648067947210655528086147 39972101920815983292129221)
                  ·
                    refine ⟨7494769110152996867274229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39972101920815983292129221 7494769110152996867274229)
                    ·
                      refine ⟨702634604076843456306959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7494769110152996867274229 702634604076843456306959)
                      ·
                        rfl

theorem cell23_1368376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1368376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368376 prefixEnd_1368376 := by exact prefixLift 1368376
  have htrace : WordTrace (prefixWord ++ tailWord_1368376) baseStart_1368376 baseEnd_1368376 := by
    simpa [prefixWord, tailWord_1368376, baseEnd_1368376] using wordTrace_append hprefix tailTrace_1368376
  have hstable : (prefixWord ++ tailWord_1368376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368376).length < 2 ^ (prefixWord ++ tailWord_1368376).sum := by decide
  have hdescent : baseEnd_1368376 < baseStart_1368376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368437 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_1368437 : Nat := 118140960795 + 1368437 * 2 ^ 59
def prefixEnd_1368437 : Nat := 4983230072969 + 3 ^ 40 * 1368437 * 2
def baseEnd_1368437 : Nat := 702665926396767717644179

theorem tailTrace_1368437 : CollatzResearch.WordTrace tailWord_1368437 prefixEnd_1368437 702665926396767717644179 := by
  unfold tailWord_1368437
  simp only [CollatzResearch.WordTrace]
  refine ⟨49910997743393934278071565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33273998495595956185381043 49910997743393934278071565)
  ·
    refine ⟨18716624153772725354276837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49910997743393934278071565 18716624153772725354276837)
    ·
      refine ⟨3509367028832386003926907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18716624153772725354276837 3509367028832386003926907)
      ·
        refine ⟨5264050543248579005890361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509367028832386003926907 5264050543248579005890361)
        ·
          refine ⟨3948037907436434254417771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5264050543248579005890361 3948037907436434254417771)
          ·
            refine ⟨5922056861154651381626657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948037907436434254417771 5922056861154651381626657)
            ·
              refine ⟨4441542645865988536219993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922056861154651381626657 4441542645865988536219993)
              ·
                refine ⟨3331156984399491402164995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4441542645865988536219993 3331156984399491402164995)
                ·
                  refine ⟨4996735476599237103247493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331156984399491402164995 4996735476599237103247493)
                  ·
                    refine ⟨936887901862356956858905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4996735476599237103247493 936887901862356956858905)
                    ·
                      refine ⟨702665926396767717644179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 936887901862356956858905 702665926396767717644179)
                      ·
                        rfl

theorem cell23_1368437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_1368437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368437 prefixEnd_1368437 := by exact prefixLift 1368437
  have htrace : WordTrace (prefixWord ++ tailWord_1368437) baseStart_1368437 baseEnd_1368437 := by
    simpa [prefixWord, tailWord_1368437, baseEnd_1368437] using wordTrace_append hprefix tailTrace_1368437
  have hstable : (prefixWord ++ tailWord_1368437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368437).length < 2 ^ (prefixWord ++ tailWord_1368437).sum := by decide
  have hdescent : baseEnd_1368437 < baseStart_1368437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368460 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 5]
def baseStart_1368460 : Nat := 118140960795 + 1368460 * 2 ^ 59
def prefixEnd_1368460 : Nat := 4983230072969 + 3 ^ 40 * 1368460 * 2
def baseEnd_1368460 : Nat := 78075304050202347517397

theorem tailTrace_1368460 : CollatzResearch.WordTrace tailWord_1368460 prefixEnd_1368460 78075304050202347517397 := by
  unfold tailWord_1368460
  simp only [CollatzResearch.WordTrace]
  refine ⟨24955918311155304603079417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33274557748207072804105889 24955918311155304603079417)
  ·
    refine ⟨18716938733366478452309563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24955918311155304603079417 18716938733366478452309563)
    ·
      refine ⟨28075408100049717678464345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716938733366478452309563 28075408100049717678464345)
      ·
        refine ⟨21056556075037288258848259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28075408100049717678464345 21056556075037288258848259)
        ·
          refine ⟨31584834112555932388272389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21056556075037288258848259 31584834112555932388272389)
          ·
            refine ⟨5922156396104237322801073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31584834112555932388272389 5922156396104237322801073)
            ·
              refine ⟨4441617297078177992100805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5922156396104237322801073 4441617297078177992100805)
              ·
                refine ⟨832803243202158373518901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4441617297078177992100805 832803243202158373518901)
                ·
                  refine ⟨78075304050202347517397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 832803243202158373518901 78075304050202347517397)
                  ·
                    rfl

theorem cell23_1368460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_1368460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368460 prefixEnd_1368460 := by exact prefixLift 1368460
  have htrace : WordTrace (prefixWord ++ tailWord_1368460) baseStart_1368460 baseEnd_1368460 := by
    simpa [prefixWord, tailWord_1368460, baseEnd_1368460] using wordTrace_append hprefix tailTrace_1368460
  have hstable : (prefixWord ++ tailWord_1368460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368460).length < 2 ^ (prefixWord ++ tailWord_1368460).sum := by decide
  have hdescent : baseEnd_1368460 < baseStart_1368460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368510 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1368510 : Nat := 118140960795 + 1368510 * 2 ^ 59
def prefixEnd_1368510 : Nat := 4983230072969 + 3 ^ 40 * 1368510 * 2
def baseEnd_1368510 : Nat := 702703410484545932031343

theorem tailTrace_1368510 : CollatzResearch.WordTrace tailWord_1368510 prefixEnd_1368510 702703410484545932031343 := by
  unfold tailWord_1368510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239207534016183468184873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33275773514752978496985989 6239207534016183468184873)
  ·
    refine ⟨4679405650512137601138655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6239207534016183468184873 4679405650512137601138655)
    ·
      refine ⟨7019108475768206401707983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4679405650512137601138655 7019108475768206401707983)
      ·
        refine ⟨10528662713652309602561975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019108475768206401707983 10528662713652309602561975)
        ·
          refine ⟨15792994070478464403842963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10528662713652309602561975 15792994070478464403842963)
          ·
            refine ⟨23689491105717696605764445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15792994070478464403842963 23689491105717696605764445)
            ·
              refine ⟨8883559164644136227161667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23689491105717696605764445 8883559164644136227161667)
              ·
                refine ⟨13325338746966204340742501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8883559164644136227161667 13325338746966204340742501)
                ·
                  refine ⟨2498501015056163313889219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13325338746966204340742501 2498501015056163313889219)
                  ·
                    refine ⟨3747751522584244970833829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2498501015056163313889219 3747751522584244970833829)
                    ·
                      refine ⟨702703410484545932031343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3747751522584244970833829 702703410484545932031343)
                      ·
                        rfl

theorem cell23_1368510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1368510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368510 prefixEnd_1368510 := by exact prefixLift 1368510
  have htrace : WordTrace (prefixWord ++ tailWord_1368510) baseStart_1368510 baseEnd_1368510 := by
    simpa [prefixWord, tailWord_1368510, baseEnd_1368510] using wordTrace_append hprefix tailTrace_1368510
  have hstable : (prefixWord ++ tailWord_1368510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368510).length < 2 ^ (prefixWord ++ tailWord_1368510).sum := by decide
  have hdescent : baseEnd_1368510 < baseStart_1368510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368604 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_1368604 : Nat := 118140960795 + 1368604 * 2 ^ 59
def prefixEnd_1368604 : Nat := 4983230072969 + 3 ^ 40 * 1368604 * 2
def baseEnd_1368604 : Nat := 702751677666068564255911

theorem tailTrace_1368604 : CollatzResearch.WordTrace tailWord_1368604 prefixEnd_1368604 702751677666068564255911 := by
  unfold tailWord_1368604
  simp only [CollatzResearch.WordTrace]
  refine ⟨24958544366894460899700433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33278059155859281199600577 24958544366894460899700433)
  ·
    refine ⟨18718908275170845674775325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24958544366894460899700433 18718908275170845674775325)
    ·
      refine ⟨7019590603189067128040747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18718908275170845674775325 7019590603189067128040747)
      ·
        refine ⟨10529385904783600692061121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019590603189067128040747 10529385904783600692061121)
        ·
          refine ⟨7897039428587700519045841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10529385904783600692061121 7897039428587700519045841)
          ·
            refine ⟨5922779571440775389284381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7897039428587700519045841 5922779571440775389284381)
            ·
              refine ⟨2221042339290290770981643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5922779571440775389284381 2221042339290290770981643)
              ·
                refine ⟨3331563508935436156472465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221042339290290770981643 3331563508935436156472465)
                ·
                  refine ⟨2498672631701577117354349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331563508935436156472465 2498672631701577117354349)
                  ·
                    refine ⟨937002236888091419007881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2498672631701577117354349 937002236888091419007881)
                    ·
                      refine ⟨702751677666068564255911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937002236888091419007881 702751677666068564255911)
                      ·
                        rfl

theorem cell23_1368604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_1368604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368604 prefixEnd_1368604 := by exact prefixLift 1368604
  have htrace : WordTrace (prefixWord ++ tailWord_1368604) baseStart_1368604 baseEnd_1368604 := by
    simpa [prefixWord, tailWord_1368604, baseEnd_1368604] using wordTrace_append hprefix tailTrace_1368604
  have hstable : (prefixWord ++ tailWord_1368604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368604).length < 2 ^ (prefixWord ++ tailWord_1368604).sum := by decide
  have hdescent : baseEnd_1368604 < baseStart_1368604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368611 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 1, 1, 3]
def baseStart_1368611 : Nat := 118140960795 + 1368611 * 2 ^ 59
def prefixEnd_1368611 : Nat := 4983230072969 + 3 ^ 40 * 1368611 * 2
def baseEnd_1368611 : Nat := 702755272030650036868379

theorem tailTrace_1368611 : CollatzResearch.WordTrace tailWord_1368611 prefixEnd_1368611 702755272030650036868379 := by
  unfold tailWord_1368611
  simp only [CollatzResearch.WordTrace]
  refine ⟨49917344044763561994905687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33278229363175707996603791 49917344044763561994905687)
  ·
    refine ⟨74876016067145342992358531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49917344044763561994905687 74876016067145342992358531)
    ·
      refine ⟨112314024100718014488537797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74876016067145342992358531 112314024100718014488537797)
      ·
        refine ⟨21058879518884627716600837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112314024100718014488537797 21058879518884627716600837)
        ·
          refine ⟨3948539909790867696862657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21058879518884627716600837 3948539909790867696862657)
          ·
            refine ⟨2961404932343150772646993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3948539909790867696862657 2961404932343150772646993)
            ·
              refine ⟨2221053699257363079485245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961404932343150772646993 2221053699257363079485245)
              ·
                refine ⟨832895137221511154806967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2221053699257363079485245 832895137221511154806967)
                ·
                  refine ⟨1249342705832266732210451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832895137221511154806967 1249342705832266732210451)
                  ·
                    refine ⟨1874014058748400098315677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1249342705832266732210451 1874014058748400098315677)
                    ·
                      refine ⟨702755272030650036868379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1874014058748400098315677 702755272030650036868379)
                      ·
                        rfl

theorem cell23_1368611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_1368611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368611 prefixEnd_1368611 := by exact prefixLift 1368611
  have htrace : WordTrace (prefixWord ++ tailWord_1368611) baseStart_1368611 baseEnd_1368611 := by
    simpa [prefixWord, tailWord_1368611, baseEnd_1368611] using wordTrace_append hprefix tailTrace_1368611
  have hstable : (prefixWord ++ tailWord_1368611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368611).length < 2 ^ (prefixWord ++ tailWord_1368611).sum := by decide
  have hdescent : baseEnd_1368611 < baseStart_1368611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368628 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1368628 : Nat := 118140960795 + 1368628 * 2 ^ 59
def prefixEnd_1368628 : Nat := 4983230072969 + 3 ^ 40 * 1368628 * 2
def baseEnd_1368628 : Nat := 702764001201776470355801

theorem tailTrace_1368628 : CollatzResearch.WordTrace tailWord_1368628 prefixEnd_1368628 702764001201776470355801 := by
  unfold tailWord_1368628
  simp only [CollatzResearch.WordTrace]
  refine ⟨24958982042850986949137269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33278642723801315932183025 24958982042850986949137269)
  ·
    refine ⟨2339904566517280026481619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24958982042850986949137269 2339904566517280026481619)
    ·
      refine ⟨3509856849775920039722429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339904566517280026481619 3509856849775920039722429)
      ·
        refine ⟨1316196318665970014895911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3509856849775920039722429 1316196318665970014895911)
        ·
          refine ⟨1974294477998955022343867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316196318665970014895911 1974294477998955022343867)
          ·
            refine ⟨2961441716998432533515801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974294477998955022343867 2961441716998432533515801)
            ·
              refine ⟨2221081287748824400136851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2961441716998432533515801 2221081287748824400136851)
              ·
                refine ⟨3331621931623236600205277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221081287748824400136851 3331621931623236600205277)
                ·
                  refine ⟨1249358224358713725076979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3331621931623236600205277 1249358224358713725076979)
                  ·
                    refine ⟨1874037336538070587615469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1249358224358713725076979 1874037336538070587615469)
                    ·
                      refine ⟨702764001201776470355801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1874037336538070587615469 702764001201776470355801)
                      ·
                        rfl

theorem cell23_1368628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1368628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368628 prefixEnd_1368628 := by exact prefixLift 1368628
  have htrace : WordTrace (prefixWord ++ tailWord_1368628) baseStart_1368628 baseEnd_1368628 := by
    simpa [prefixWord, tailWord_1368628, baseEnd_1368628] using wordTrace_append hprefix tailTrace_1368628
  have hstable : (prefixWord ++ tailWord_1368628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368628).length < 2 ^ (prefixWord ++ tailWord_1368628).sum := by decide
  have hdescent : baseEnd_1368628 < baseStart_1368628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368634 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_1368634 : Nat := 118140960795 + 1368634 * 2 ^ 59
def prefixEnd_1368634 : Nat := 4983230072969 + 3 ^ 40 * 1368634 * 2
def baseEnd_1368634 : Nat := 702767082085703446880773

theorem tailTrace_1368634 : CollatzResearch.WordTrace tailWord_1368634 prefixEnd_1368634 702767082085703446880773 := by
  unfold tailWord_1368634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479545730920059230748239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33278788615786824615328637 12479545730920059230748239)
  ·
    refine ⟨18719318596380088846122359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12479545730920059230748239 18719318596380088846122359)
    ·
      refine ⟨28078977894570133269183539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18719318596380088846122359 28078977894570133269183539)
      ·
        refine ⟨42118466841855199903775309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28078977894570133269183539 42118466841855199903775309)
        ·
          refine ⟨15794425065695699963915741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42118466841855199903775309 15794425065695699963915741)
          ·
            refine ⟨5922909399635887486468403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15794425065695699963915741 5922909399635887486468403)
            ·
              refine ⟨8884364099453831229702605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5922909399635887486468403 8884364099453831229702605)
              ·
                refine ⟨3331636537295186711138477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8884364099453831229702605 3331636537295186711138477)
                ·
                  refine ⟨1249363701485695016676929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3331636537295186711138477 1249363701485695016676929)
                  ·
                    refine ⟨937022776114271262507697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1249363701485695016676929 937022776114271262507697)
                    ·
                      refine ⟨702767082085703446880773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937022776114271262507697 702767082085703446880773)
                      ·
                        rfl

theorem cell23_1368634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_1368634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368634 prefixEnd_1368634 := by exact prefixLift 1368634
  have htrace : WordTrace (prefixWord ++ tailWord_1368634) baseStart_1368634 baseEnd_1368634 := by
    simpa [prefixWord, tailWord_1368634, baseEnd_1368634] using wordTrace_append hprefix tailTrace_1368634
  have hstable : (prefixWord ++ tailWord_1368634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368634).length < 2 ^ (prefixWord ++ tailWord_1368634).sum := by decide
  have hdescent : baseEnd_1368634 < baseStart_1368634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368637 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1368637 : Nat := 118140960795 + 1368637 * 2 ^ 59
def prefixEnd_1368637 : Nat := 4983230072969 + 3 ^ 40 * 1368637 * 2
def baseEnd_1368637 : Nat := 702768622527666935143259

theorem tailTrace_1368637 : CollatzResearch.WordTrace tailWord_1368637 prefixEnd_1368637 702768622527666935143259 := by
  unfold tailWord_1368637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49918292342669368435352165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33278861561779578956901443 49918292342669368435352165)
  ·
    refine ⟨9359679814250506581628531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49918292342669368435352165 9359679814250506581628531)
    ·
      refine ⟨14039519721375759872442797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359679814250506581628531 14039519721375759872442797)
      ·
        refine ⟨5264819895515909952166049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14039519721375759872442797 5264819895515909952166049)
        ·
          refine ⟨3948614921636932464124537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5264819895515909952166049 3948614921636932464124537)
          ·
            refine ⟨2961461191227699348093403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3948614921636932464124537 2961461191227699348093403)
            ·
              refine ⟨4442191786841549022140105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961461191227699348093403 4442191786841549022140105)
              ·
                refine ⟨3331643840131161766605079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4442191786841549022140105 3331643840131161766605079)
                ·
                  refine ⟨4997465760196742649907619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331643840131161766605079 4997465760196742649907619)
                  ·
                    refine ⟨7496198640295113974861429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4997465760196742649907619 7496198640295113974861429)
                    ·
                      refine ⟨702768622527666935143259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7496198640295113974861429 702768622527666935143259)
                      ·
                        rfl

theorem cell23_1368637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1368637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368637 prefixEnd_1368637 := by exact prefixLift 1368637
  have htrace : WordTrace (prefixWord ++ tailWord_1368637) baseStart_1368637 baseEnd_1368637 := by
    simpa [prefixWord, tailWord_1368637, baseEnd_1368637] using wordTrace_append hprefix tailTrace_1368637
  have hstable : (prefixWord ++ tailWord_1368637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368637).length < 2 ^ (prefixWord ++ tailWord_1368637).sum := by decide
  have hdescent : baseEnd_1368637 < baseStart_1368637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368647 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1368647 : Nat := 118140960795 + 1368647 * 2 ^ 59
def prefixEnd_1368647 : Nat := 4983230072969 + 3 ^ 40 * 1368647 * 2
def baseEnd_1368647 : Nat := 702773757334211896018213

theorem tailTrace_1368647 : CollatzResearch.WordTrace tailWord_1368647 prefixEnd_1368647 702773757334211896018213 := by
  unfold tailWord_1368647
  simp only [CollatzResearch.WordTrace]
  refine ⟨49918657072633140143216195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33279104715088760095477463 49918657072633140143216195)
  ·
    refine ⟨74877985608949710214824293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49918657072633140143216195 74877985608949710214824293)
    ·
      refine ⟨14039622301678070665279555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74877985608949710214824293 14039622301678070665279555)
      ·
        refine ⟨21059433452517105997919333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14039622301678070665279555 21059433452517105997919333)
        ·
          refine ⟨3948643772346957374609875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21059433452517105997919333 3948643772346957374609875)
          ·
            refine ⟨5922965658520436061914813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948643772346957374609875 5922965658520436061914813)
            ·
              refine ⟨2221112121945163523218055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5922965658520436061914813 2221112121945163523218055)
              ·
                refine ⟨3331668182917745284827083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221112121945163523218055 3331668182917745284827083)
                ·
                  refine ⟨4997502274376617927240625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331668182917745284827083 4997502274376617927240625)
                  ·
                    refine ⟨3748126705782463445430469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997502274376617927240625 3748126705782463445430469)
                    ·
                      refine ⟨702773757334211896018213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3748126705782463445430469 702773757334211896018213)
                      ·
                        rfl

theorem cell23_1368647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1368647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368647 prefixEnd_1368647 := by exact prefixLift 1368647
  have htrace : WordTrace (prefixWord ++ tailWord_1368647) baseStart_1368647 baseEnd_1368647 := by
    simpa [prefixWord, tailWord_1368647, baseEnd_1368647] using wordTrace_append hprefix tailTrace_1368647
  have hstable : (prefixWord ++ tailWord_1368647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368647).length < 2 ^ (prefixWord ++ tailWord_1368647).sum := by decide
  have hdescent : baseEnd_1368647 < baseStart_1368647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368657 : List Nat := [1, 2, 2, 1, 3, 5, 2, 7]
def baseStart_1368657 : Nat := 118140960795 + 1368657 * 2 ^ 59
def prefixEnd_1368657 : Nat := 4983230072969 + 3 ^ 40 * 1368657 * 2
def baseEnd_1368657 : Nat := 26028847857065068773821

theorem tailTrace_1368657 : CollatzResearch.WordTrace tailWord_1368657 prefixEnd_1368657 26028847857065068773821 := by
  unfold tailWord_1368657
  simp only [CollatzResearch.WordTrace]
  refine ⟨49919021802596911851080225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33279347868397941234053483 49919021802596911851080225)
  ·
    refine ⟨37439266351947683888310169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49919021802596911851080225 37439266351947683888310169)
    ·
      refine ⟨28079449763960762916232627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37439266351947683888310169 28079449763960762916232627)
      ·
        refine ⟨42119174645941144374348941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28079449763960762916232627 42119174645941144374348941)
        ·
          refine ⟨15794690492227929140380853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42119174645941144374348941 15794690492227929140380853)
          ·
            refine ⟨1480752233646368356910705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15794690492227929140380853 1480752233646368356910705)
            ·
              refine ⟨1110564175234776267683029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1480752233646368356910705 1110564175234776267683029)
              ·
                refine ⟨26028847857065068773821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1110564175234776267683029 26028847857065068773821)
                ·
                  rfl

theorem cell23_1368657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 7].length) (baseStart_1368657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368657 prefixEnd_1368657 := by exact prefixLift 1368657
  have htrace : WordTrace (prefixWord ++ tailWord_1368657) baseStart_1368657 baseEnd_1368657 := by
    simpa [prefixWord, tailWord_1368657, baseEnd_1368657] using wordTrace_append hprefix tailTrace_1368657
  have hstable : (prefixWord ++ tailWord_1368657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368657).length < 2 ^ (prefixWord ++ tailWord_1368657).sum := by decide
  have hdescent : baseEnd_1368657 < baseStart_1368657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368674 : List Nat := [3, 3, 2, 3, 1, 2, 9]
def baseStart_1368674 : Nat := 118140960795 + 1368674 * 2 ^ 59
def prefixEnd_1368674 : Nat := 4983230072969 + 3 ^ 40 * 1368674 * 2
def baseEnd_1368674 : Nat := 8676390386566460375069

theorem tailTrace_1368674 : CollatzResearch.WordTrace tailWord_1368674 prefixEnd_1368674 8676390386566460375069 := by
  unfold tailWord_1368674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479910460883830938612269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33279761229023549169632717 12479910460883830938612269)
  ·
    refine ⟨4679966422831436601979601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12479910460883830938612269 4679966422831436601979601)
    ·
      refine ⟨3509974817123577451484701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4679966422831436601979601 3509974817123577451484701)
      ·
        refine ⟨1316240556421341544306763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3509974817123577451484701 1316240556421341544306763)
        ·
          refine ⟨1974360834632012316460145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316240556421341544306763 1974360834632012316460145)
          ·
            refine ⟨1480770625974009237345109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1974360834632012316460145 1480770625974009237345109)
            ·
              refine ⟨8676390386566460375069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1480770625974009237345109 8676390386566460375069)
              ·
                rfl

theorem cell23_1368674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 9].length) (baseStart_1368674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368674 prefixEnd_1368674 := by exact prefixLift 1368674
  have htrace : WordTrace (prefixWord ++ tailWord_1368674) baseStart_1368674 baseEnd_1368674 := by
    simpa [prefixWord, tailWord_1368674, baseEnd_1368674] using wordTrace_append hprefix tailTrace_1368674
  have hstable : (prefixWord ++ tailWord_1368674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368674).length < 2 ^ (prefixWord ++ tailWord_1368674).sum := by decide
  have hdescent : baseEnd_1368674 < baseStart_1368674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368685 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1368685 : Nat := 118140960795 + 1368685 * 2 ^ 59
def prefixEnd_1368685 : Nat := 4983230072969 + 3 ^ 40 * 1368685 * 2
def baseEnd_1368685 : Nat := 702793269599082747343039

theorem tailTrace_1368685 : CollatzResearch.WordTrace tailWord_1368685 prefixEnd_1368685 702793269599082747343039 := by
  unfold tailWord_1368685
  simp only [CollatzResearch.WordTrace]
  refine ⟨49920043046495472633099509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33280028697663648422066339 49920043046495472633099509)
  ·
    refine ⟨4680004035608950559353079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49920043046495472633099509 4680004035608950559353079)
    ·
      refine ⟨7020006053413425839029619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4680004035608950559353079 7020006053413425839029619)
      ·
        refine ⟨10530009080120138758544429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7020006053413425839029619 10530009080120138758544429)
        ·
          refine ⟨3948753405045052034454161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10530009080120138758544429 3948753405045052034454161)
          ·
            refine ⟨2961565053783789025840621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3948753405045052034454161 2961565053783789025840621)
            ·
              refine ⟨1110586895168920884690233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2961565053783789025840621 1110586895168920884690233)
              ·
                refine ⟨832940171376690663517675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110586895168920884690233 832940171376690663517675)
                ·
                  refine ⟨1249410257065035995276513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832940171376690663517675 1249410257065035995276513)
                  ·
                    refine ⟨937057692798776996457385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1249410257065035995276513 937057692798776996457385)
                    ·
                      refine ⟨702793269599082747343039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937057692798776996457385 702793269599082747343039)
                      ·
                        rfl

theorem cell23_1368685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1368685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368685 prefixEnd_1368685 := by exact prefixLift 1368685
  have htrace : WordTrace (prefixWord ++ tailWord_1368685) baseStart_1368685 baseEnd_1368685 := by
    simpa [prefixWord, tailWord_1368685, baseEnd_1368685] using wordTrace_append hprefix tailTrace_1368685
  have hstable : (prefixWord ++ tailWord_1368685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368685).length < 2 ^ (prefixWord ++ tailWord_1368685).sum := by decide
  have hdescent : baseEnd_1368685 < baseStart_1368685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368700 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1368700 : Nat := 118140960795 + 1368700 * 2 ^ 59
def prefixEnd_1368700 : Nat := 4983230072969 + 3 ^ 40 * 1368700 * 2
def baseEnd_1368700 : Nat := 234266990602966729551823

theorem tailTrace_1368700 : CollatzResearch.WordTrace tailWord_1368700 prefixEnd_1368700 234266990602966729551823 := by
  unfold tailWord_1368700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960295070720565097447777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33280393427627420129930369 24960295070720565097447777)
  ·
    refine ⟨18720221303040423823085833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24960295070720565097447777 18720221303040423823085833)
    ·
      refine ⟨14040165977280317867314375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18720221303040423823085833 14040165977280317867314375)
      ·
        refine ⟨21060248965920476800971563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14040165977280317867314375 21060248965920476800971563)
        ·
          refine ⟨31590373448880715201457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060248965920476800971563 31590373448880715201457345)
          ·
            refine ⟨23692780086660536401093009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31590373448880715201457345 23692780086660536401093009)
            ·
              refine ⟨17769585064995402300819757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23692780086660536401093009 17769585064995402300819757)
              ·
                refine ⟨6663594399373275862807409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17769585064995402300819757 6663594399373275862807409)
                ·
                  refine ⟨4997695799529956897105557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663594399373275862807409 4997695799529956897105557)
                  ·
                    refine ⟨234266990602966729551823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4997695799529956897105557 234266990602966729551823)
                    ·
                      rfl

theorem cell23_1368700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1368700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368700 prefixEnd_1368700 := by exact prefixLift 1368700
  have htrace : WordTrace (prefixWord ++ tailWord_1368700) baseStart_1368700 baseEnd_1368700 := by
    simpa [prefixWord, tailWord_1368700, baseEnd_1368700] using wordTrace_append hprefix tailTrace_1368700
  have hstable : (prefixWord ++ tailWord_1368700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368700).length < 2 ^ (prefixWord ++ tailWord_1368700).sum := by decide
  have hdescent : baseEnd_1368700 < baseStart_1368700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368701 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_1368701 : Nat := 118140960795 + 1368701 * 2 ^ 59
def prefixEnd_1368701 : Nat := 4983230072969 + 3 ^ 40 * 1368701 * 2
def baseEnd_1368701 : Nat := 702801485289554684742965

theorem tailTrace_1368701 : CollatzResearch.WordTrace tailWord_1368701 prefixEnd_1368701 702801485289554684742965 := by
  unfold tailWord_1368701
  simp only [CollatzResearch.WordTrace]
  refine ⟨49920626614437507365681957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33280417742958338243787971 49920626614437507365681957)
  ·
    refine ⟨9360117490207032631065367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49920626614437507365681957 9360117490207032631065367)
    ·
      refine ⟨14040176235310548946598051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360117490207032631065367 14040176235310548946598051)
      ·
        refine ⟨21060264352965823419897077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14040176235310548946598051 21060264352965823419897077)
        ·
          refine ⟨1974399783090545945615351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21060264352965823419897077 1974399783090545945615351)
          ·
            refine ⟨2961599674635818918423027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1974399783090545945615351 2961599674635818918423027)
            ·
              refine ⟨4442399511953728377634541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2961599674635818918423027 4442399511953728377634541)
              ·
                refine ⟨1665899816982648141612953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4442399511953728377634541 1665899816982648141612953)
                ·
                  refine ⟨1249424862736986106209715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1665899816982648141612953 1249424862736986106209715)
                  ·
                    refine ⟨1874137294105479159314573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1249424862736986106209715 1874137294105479159314573)
                    ·
                      refine ⟨702801485289554684742965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1874137294105479159314573 702801485289554684742965)
                      ·
                        rfl

theorem cell23_1368701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_1368701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368701 prefixEnd_1368701 := by exact prefixLift 1368701
  have htrace : WordTrace (prefixWord ++ tailWord_1368701) baseStart_1368701 baseEnd_1368701 := by
    simpa [prefixWord, tailWord_1368701, baseEnd_1368701] using wordTrace_append hprefix tailTrace_1368701
  have hstable : (prefixWord ++ tailWord_1368701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368701).length < 2 ^ (prefixWord ++ tailWord_1368701).sum := by decide
  have hdescent : baseEnd_1368701 < baseStart_1368701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368720 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_1368720 : Nat := 118140960795 + 1368720 * 2 ^ 59
def prefixEnd_1368720 : Nat := 4983230072969 + 3 ^ 40 * 1368720 * 2
def baseEnd_1368720 : Nat := 702811241421990110405377

theorem tailTrace_1368720 : CollatzResearch.WordTrace tailWord_1368720 prefixEnd_1368720 702811241421990110405377 := by
  unfold tailWord_1368720
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960659800684336805311807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33280879734245782407082409 24960659800684336805311807)
  ·
    refine ⟨37440989701026505207967711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24960659800684336805311807 37440989701026505207967711)
    ·
      refine ⟨56161484551539757811951567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37440989701026505207967711 56161484551539757811951567)
      ·
        refine ⟨84242226827309636717927351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56161484551539757811951567 84242226827309636717927351)
        ·
          refine ⟨126363340240964455076891027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84242226827309636717927351 126363340240964455076891027)
          ·
            refine ⟨189545010361446682615336541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126363340240964455076891027 189545010361446682615336541)
            ·
              refine ⟨71079378885542505980751203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189545010361446682615336541 71079378885542505980751203)
              ·
                refine ⟨106619068328313758971126805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71079378885542505980751203 106619068328313758971126805)
                ·
                  refine ⟨4997768827889707451771569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106619068328313758971126805 4997768827889707451771569)
                  ·
                    refine ⟨3748326620917280588828677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997768827889707451771569 3748326620917280588828677)
                    ·
                      refine ⟨702811241421990110405377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3748326620917280588828677 702811241421990110405377)
                      ·
                        rfl

theorem cell23_1368720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_1368720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368720 prefixEnd_1368720 := by exact prefixLift 1368720
  have htrace : WordTrace (prefixWord ++ tailWord_1368720) baseStart_1368720 baseEnd_1368720 := by
    simpa [prefixWord, tailWord_1368720, baseEnd_1368720] using wordTrace_append hprefix tailTrace_1368720
  have hstable : (prefixWord ++ tailWord_1368720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368720).length < 2 ^ (prefixWord ++ tailWord_1368720).sum := by decide
  have hdescent : baseEnd_1368720 < baseStart_1368720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368817 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_1368817 : Nat := 118140960795 + 1368817 * 2 ^ 59
def prefixEnd_1368817 : Nat := 4983230072969 + 3 ^ 40 * 1368817 * 2
def baseEnd_1368817 : Nat := 702861049045476230892431

theorem tailTrace_1368817 : CollatzResearch.WordTrace tailWord_1368817 prefixEnd_1368817 702861049045476230892431 := by
  unfold tailWord_1368817
  simp only [CollatzResearch.WordTrace]
  refine ⟨49924857482017259176904705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33283238321344839451269803 49924857482017259176904705)
  ·
    refine ⟨37443643111512944382678529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49924857482017259176904705 37443643111512944382678529)
    ·
      refine ⟨28082732333634708287008897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37443643111512944382678529 28082732333634708287008897)
      ·
        refine ⟨21062049250226031215256673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28082732333634708287008897 21062049250226031215256673)
        ·
          refine ⟨15796536937669523411442505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21062049250226031215256673 15796536937669523411442505)
          ·
            refine ⟨11847402703252142558581879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15796536937669523411442505 11847402703252142558581879)
            ·
              refine ⟨17771104054878213837872819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11847402703252142558581879 17771104054878213837872819)
              ·
                refine ⟨26656656082317320756809229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17771104054878213837872819 26656656082317320756809229)
                ·
                  refine ⟨9996246030868995283803461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26656656082317320756809229 9996246030868995283803461)
                  ·
                    refine ⟨1874296130787936615713149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9996246030868995283803461 1874296130787936615713149)
                    ·
                      refine ⟨702861049045476230892431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1874296130787936615713149 702861049045476230892431)
                      ·
                        rfl

theorem cell23_1368817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_1368817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368817 prefixEnd_1368817 := by exact prefixLift 1368817
  have htrace : WordTrace (prefixWord ++ tailWord_1368817) baseStart_1368817 baseEnd_1368817 := by
    simpa [prefixWord, tailWord_1368817, baseEnd_1368817] using wordTrace_append hprefix tailTrace_1368817
  have hstable : (prefixWord ++ tailWord_1368817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368817).length < 2 ^ (prefixWord ++ tailWord_1368817).sum := by decide
  have hdescent : baseEnd_1368817 < baseStart_1368817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368841 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 1, 4]
def baseStart_1368841 : Nat := 118140960795 + 1368841 * 2 ^ 59
def prefixEnd_1368841 : Nat := 4983230072969 + 3 ^ 40 * 1368841 * 2
def baseEnd_1368841 : Nat := 234291124193728045664107

theorem tailTrace_1368841 : CollatzResearch.WordTrace tailWord_1368841 prefixEnd_1368841 234291124193728045664107 := by
  unfold tailWord_1368841
  simp only [CollatzResearch.WordTrace]
  refine ⟨49925732833930311275778377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33283821889286874183852251 49925732833930311275778377)
  ·
    refine ⟨37444299625447733456833783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49925732833930311275778377 37444299625447733456833783)
    ·
      refine ⟨56166449438171600185250675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37444299625447733456833783 56166449438171600185250675)
      ·
        refine ⟨84249674157257400277876013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56166449438171600185250675 84249674157257400277876013)
        ·
          refine ⟨31593627808971525104203505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84249674157257400277876013 31593627808971525104203505)
          ·
            refine ⟨23695220856728643828152629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31593627808971525104203505 23695220856728643828152629)
            ·
              refine ⟨2221426955318310358889309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23695220856728643828152629 2221426955318310358889309)
              ·
                refine ⟨833035108244366384583491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2221426955318310358889309 833035108244366384583491)
                ·
                  refine ⟨1249552662366549576875237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833035108244366384583491 1249552662366549576875237)
                  ·
                    refine ⟨234291124193728045664107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249552662366549576875237 234291124193728045664107)
                    ·
                      rfl

theorem cell23_1368841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 4].length) (baseStart_1368841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368841 prefixEnd_1368841 := by exact prefixLift 1368841
  have htrace : WordTrace (prefixWord ++ tailWord_1368841) baseStart_1368841 baseEnd_1368841 := by
    simpa [prefixWord, tailWord_1368841, baseEnd_1368841] using wordTrace_append hprefix tailTrace_1368841
  have hstable : (prefixWord ++ tailWord_1368841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368841).length < 2 ^ (prefixWord ++ tailWord_1368841).sum := by decide
  have hdescent : baseEnd_1368841 < baseStart_1368841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368858 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_1368858 : Nat := 118140960795 + 1368858 * 2 ^ 59
def prefixEnd_1368858 : Nat := 4983230072969 + 3 ^ 40 * 1368858 * 2
def baseEnd_1368858 : Nat := 234294033917436856826581

theorem tailTrace_1368858 : CollatzResearch.WordTrace tailWord_1368858 prefixEnd_1368858 234294033917436856826581 := by
  unfold tailWord_1368858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481588218717180794786807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33284235249912482119431485 12481588218717180794786807)
  ·
    refine ⟨18722382328075771192180211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12481588218717180794786807 18722382328075771192180211)
    ·
      refine ⟨28083573492113656788270317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18722382328075771192180211 28083573492113656788270317)
      ·
        refine ⟨10531340059542621295601369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28083573492113656788270317 10531340059542621295601369)
        ·
          refine ⟨7898505044656965971701027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10531340059542621295601369 7898505044656965971701027)
          ·
            refine ⟨11847757566985448957551541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898505044656965971701027 11847757566985448957551541)
            ·
              refine ⟨1110727271904885839770457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11847757566985448957551541 1110727271904885839770457)
              ·
                refine ⟨833045453928664379827843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110727271904885839770457 833045453928664379827843)
                ·
                  refine ⟨1249568180892996569741765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833045453928664379827843 1249568180892996569741765)
                  ·
                    refine ⟨234294033917436856826581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249568180892996569741765 234294033917436856826581)
                    ·
                      rfl

theorem cell23_1368858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_1368858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368858 prefixEnd_1368858 := by exact prefixLift 1368858
  have htrace : WordTrace (prefixWord ++ tailWord_1368858) baseStart_1368858 baseEnd_1368858 := by
    simpa [prefixWord, tailWord_1368858, baseEnd_1368858] using wordTrace_append hprefix tailTrace_1368858
  have hstable : (prefixWord ++ tailWord_1368858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368858).length < 2 ^ (prefixWord ++ tailWord_1368858).sum := by decide
  have hdescent : baseEnd_1368858 < baseStart_1368858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368867 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 3, 5]
def baseStart_1368867 : Nat := 118140960795 + 1368867 * 2 ^ 59
def prefixEnd_1368867 : Nat := 4983230072969 + 3 ^ 40 * 1368867 * 2
def baseEnd_1368867 : Nat := 234295574359400345089067

theorem tailTrace_1368867 : CollatzResearch.WordTrace tailWord_1368867 prefixEnd_1368867 234295574359400345089067 := by
  unfold tailWord_1368867
  simp only [CollatzResearch.WordTrace]
  refine ⟨49926681131836117716224855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33284454087890745144149903 49926681131836117716224855)
  ·
    refine ⟨74890021697754176574337283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49926681131836117716224855 74890021697754176574337283)
    ·
      refine ⟨112335032546631264861505925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74890021697754176574337283 112335032546631264861505925)
      ·
        refine ⟨21062818602493362161532361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112335032546631264861505925 21062818602493362161532361)
        ·
          refine ⟨15797113951870021621149271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21062818602493362161532361 15797113951870021621149271)
          ·
            refine ⟨23695670927805032431723907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15797113951870021621149271 23695670927805032431723907)
            ·
              refine ⟨35543506391707548647585861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23695670927805032431723907 35543506391707548647585861)
              ·
                refine ⟨6664407448445165371422349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35543506391707548647585861 6664407448445165371422349)
                ·
                  refine ⟨2499152793166937014283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6664407448445165371422349 2499152793166937014283381)
                  ·
                    refine ⟨234295574359400345089067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2499152793166937014283381 234295574359400345089067)
                    ·
                      rfl

theorem cell23_1368867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 5].length) (baseStart_1368867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368867 prefixEnd_1368867 := by exact prefixLift 1368867
  have htrace : WordTrace (prefixWord ++ tailWord_1368867) baseStart_1368867 baseEnd_1368867 := by
    simpa [prefixWord, tailWord_1368867, baseEnd_1368867] using wordTrace_append hprefix tailTrace_1368867
  have hstable : (prefixWord ++ tailWord_1368867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368867).length < 2 ^ (prefixWord ++ tailWord_1368867).sum := by decide
  have hdescent : baseEnd_1368867 < baseStart_1368867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368909 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1368909 : Nat := 118140960795 + 1368909 * 2 ^ 59
def prefixEnd_1368909 : Nat := 4983230072969 + 3 ^ 40 * 1368909 * 2
def baseEnd_1368909 : Nat := 234302763088563290314003

theorem tailTrace_1368909 : CollatzResearch.WordTrace tailWord_1368909 prefixEnd_1368909 234302763088563290314003 := by
  unfold tailWord_1368909
  simp only [CollatzResearch.WordTrace]
  refine ⟨49928212997683958889253781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33285475331789305926169187 49928212997683958889253781)
  ·
    refine ⟨2340384984266435572933771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49928212997683958889253781 2340384984266435572933771)
    ·
      refine ⟨3510577476399653359400657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2340384984266435572933771 3510577476399653359400657)
      ·
        refine ⟨2632933107299740019550493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3510577476399653359400657 2632933107299740019550493)
        ·
          refine ⟨987349915237402507331435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2632933107299740019550493 987349915237402507331435)
          ·
            refine ⟨1481024872856103760997153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987349915237402507331435 1481024872856103760997153)
            ·
              refine ⟨1110768654642077820747865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481024872856103760997153 1110768654642077820747865)
              ·
                refine ⟨833076490981558365560899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110768654642077820747865 833076490981558365560899)
                ·
                  refine ⟨1249614736472337548341349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833076490981558365560899 1249614736472337548341349)
                  ·
                    refine ⟨234302763088563290314003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249614736472337548341349 234302763088563290314003)
                    ·
                      rfl

theorem cell23_1368909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1368909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368909 prefixEnd_1368909 := by exact prefixLift 1368909
  have htrace : WordTrace (prefixWord ++ tailWord_1368909) baseStart_1368909 baseEnd_1368909 := by
    simpa [prefixWord, tailWord_1368909, baseEnd_1368909] using wordTrace_append hprefix tailTrace_1368909
  have hstable : (prefixWord ++ tailWord_1368909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368909).length < 2 ^ (prefixWord ++ tailWord_1368909).sum := by decide
  have hdescent : baseEnd_1368909 < baseStart_1368909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368931 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 2, 4]
def baseStart_1368931 : Nat := 118140960795 + 1368931 * 2 ^ 59
def prefixEnd_1368931 : Nat := 4983230072969 + 3 ^ 40 * 1368931 * 2
def baseEnd_1368931 : Nat := 234306528613362928288969

theorem tailTrace_1368931 : CollatzResearch.WordTrace tailWord_1368931 prefixEnd_1368931 234306528613362928288969 := by
  unfold tailWord_1368931
  simp only [CollatzResearch.WordTrace]
  refine ⟨49929015403604256646554647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33286010269069504431036431 49929015403604256646554647)
  ·
    refine ⟨74893523105406384969831971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49929015403604256646554647 74893523105406384969831971)
    ·
      refine ⟨112340284658109577454747957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74893523105406384969831971 112340284658109577454747957)
      ·
        refine ⟨10531901686697772886382621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112340284658109577454747957 10531901686697772886382621)
        ·
          refine ⟨3949463132511664832393483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10531901686697772886382621 3949463132511664832393483)
          ·
            refine ⟨5924194698767497248590225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949463132511664832393483 5924194698767497248590225)
            ·
              refine ⟨4443146024075622936442669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5924194698767497248590225 4443146024075622936442669)
              ·
                refine ⟨1666179759028358601166001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4443146024075622936442669 1666179759028358601166001)
                ·
                  refine ⟨1249634819271268950874501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1666179759028358601166001 1249634819271268950874501)
                  ·
                    refine ⟨234306528613362928288969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249634819271268950874501 234306528613362928288969)
                    ·
                      rfl

theorem cell23_1368931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 4].length) (baseStart_1368931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368931 prefixEnd_1368931 := by exact prefixLift 1368931
  have htrace : WordTrace (prefixWord ++ tailWord_1368931) baseStart_1368931 baseEnd_1368931 := by
    simpa [prefixWord, tailWord_1368931, baseEnd_1368931] using wordTrace_append hprefix tailTrace_1368931
  have hstable : (prefixWord ++ tailWord_1368931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368931).length < 2 ^ (prefixWord ++ tailWord_1368931).sum := by decide
  have hdescent : baseEnd_1368931 < baseStart_1368931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368941 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1368941 : Nat := 118140960795 + 1368941 * 2 ^ 59
def prefixEnd_1368941 : Nat := 4983230072969 + 3 ^ 40 * 1368941 * 2
def baseEnd_1368941 : Nat := 702924720646633745741861

theorem tailTrace_1368941 : CollatzResearch.WordTrace tailWord_1368941 prefixEnd_1368941 702924720646633745741861 := by
  unfold tailWord_1368941
  simp only [CollatzResearch.WordTrace]
  refine ⟨49929380133568028354418677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33286253422378685569612451 49929380133568028354418677)
  ·
    refine ⟨4680879387522002658226751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49929380133568028354418677 4680879387522002658226751)
    ·
      refine ⟨7021319081283003987340127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4680879387522002658226751 7021319081283003987340127)
      ·
        refine ⟨10531978621924505981010191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021319081283003987340127 10531978621924505981010191)
        ·
          refine ⟨15797967932886758971515287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531978621924505981010191 15797967932886758971515287)
          ·
            refine ⟨23696951899330138457272931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15797967932886758971515287 23696951899330138457272931)
            ·
              refine ⟨35545427848995207685909397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23696951899330138457272931 35545427848995207685909397)
              ·
                refine ⟨1666191930421650360277003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35545427848995207685909397 1666191930421650360277003)
                ·
                  refine ⟨2499287895632475540415505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666191930421650360277003 2499287895632475540415505)
                  ·
                    refine ⟨1874465921724356655311629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2499287895632475540415505 1874465921724356655311629)
                    ·
                      refine ⟨702924720646633745741861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1874465921724356655311629 702924720646633745741861)
                      ·
                        rfl

theorem cell23_1368941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1368941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368941 prefixEnd_1368941 := by exact prefixLift 1368941
  have htrace : WordTrace (prefixWord ++ tailWord_1368941) baseStart_1368941 baseEnd_1368941 := by
    simpa [prefixWord, tailWord_1368941, baseEnd_1368941] using wordTrace_append hprefix tailTrace_1368941
  have hstable : (prefixWord ++ tailWord_1368941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368941).length < 2 ^ (prefixWord ++ tailWord_1368941).sum := by decide
  have hdescent : baseEnd_1368941 < baseStart_1368941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1368942 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1368942 : Nat := 118140960795 + 1368942 * 2 ^ 59
def prefixEnd_1368942 : Nat := 4983230072969 + 3 ^ 40 * 1368942 * 2
def baseEnd_1368942 : Nat := 702925234127288241829357

theorem tailTrace_1368942 : CollatzResearch.WordTrace tailWord_1368942 prefixEnd_1368942 702925234127288241829357 := by
  unfold tailWord_1368942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6241177075820550690650635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33286277737709603683470053 6241177075820550690650635)
  ·
    refine ⟨9361765613730826035975953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6241177075820550690650635 9361765613730826035975953)
    ·
      refine ⟨7021324210298119526981965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9361765613730826035975953 7021324210298119526981965)
      ·
        refine ⟨2632996578861794822618237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7021324210298119526981965 2632996578861794822618237)
        ·
          refine ⟨987373717073173058481839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2632996578861794822618237 987373717073173058481839)
          ·
            refine ⟨1481060575609759587722759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987373717073173058481839 1481060575609759587722759)
            ·
              refine ⟨2221590863414639381584139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481060575609759587722759 2221590863414639381584139)
              ·
                refine ⟨3332386295121959072376209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2221590863414639381584139 3332386295121959072376209)
                ·
                  refine ⟨2499289721341469304282157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3332386295121959072376209 2499289721341469304282157)
                  ·
                    refine ⟨937233645503050989105809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499289721341469304282157 937233645503050989105809)
                    ·
                      refine ⟨702925234127288241829357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937233645503050989105809 702925234127288241829357)
                      ·
                        rfl

theorem cell23_1368942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1368942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1368942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1368942 prefixEnd_1368942 := by exact prefixLift 1368942
  have htrace : WordTrace (prefixWord ++ tailWord_1368942) baseStart_1368942 baseEnd_1368942 := by
    simpa [prefixWord, tailWord_1368942, baseEnd_1368942] using wordTrace_append hprefix tailTrace_1368942
  have hstable : (prefixWord ++ tailWord_1368942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1368942).length < 2 ^ (prefixWord ++ tailWord_1368942).sum := by decide
  have hdescent : baseEnd_1368942 < baseStart_1368942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1368942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369064 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1369064 : Nat := 118140960795 + 1369064 * 2 ^ 59
def prefixEnd_1369064 : Nat := 4983230072969 + 3 ^ 40 * 1369064 * 2
def baseEnd_1369064 : Nat := 234329292922378921501265

theorem tailTrace_1369064 : CollatzResearch.WordTrace tailWord_1369064 prefixEnd_1369064 234329292922378921501265 := by
  unfold tailWord_1369064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24966933156061210180573123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33289244208081613574097497 24966933156061210180573123)
  ·
    refine ⟨37450399734091815270859685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24966933156061210180573123 37450399734091815270859685)
    ·
      refine ⟨7021949950142215363286191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37450399734091815270859685 7021949950142215363286191)
      ·
        refine ⟨10532924925213323044929287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021949950142215363286191 10532924925213323044929287)
        ·
          refine ⟨15799387387819984567393931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10532924925213323044929287 15799387387819984567393931)
          ·
            refine ⟨23699081081729976851090897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15799387387819984567393931 23699081081729976851090897)
            ·
              refine ⟨17774310811297482638318173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23699081081729976851090897 17774310811297482638318173)
              ·
                refine ⟨6665366554236555989369315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17774310811297482638318173 6665366554236555989369315)
                ·
                  refine ⟨9998049831354833984053973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6665366554236555989369315 9998049831354833984053973)
                  ·
                    refine ⟨234329292922378921501265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9998049831354833984053973 234329292922378921501265)
                    ·
                      rfl

theorem cell23_1369064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1369064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369064 prefixEnd_1369064 := by exact prefixLift 1369064
  have htrace : WordTrace (prefixWord ++ tailWord_1369064) baseStart_1369064 baseEnd_1369064 := by
    simpa [prefixWord, tailWord_1369064, baseEnd_1369064] using wordTrace_append hprefix tailTrace_1369064
  have hstable : (prefixWord ++ tailWord_1369064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369064).length < 2 ^ (prefixWord ++ tailWord_1369064).sum := by decide
  have hdescent : baseEnd_1369064 < baseStart_1369064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369145 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 1, 4]
def baseStart_1369145 : Nat := 118140960795 + 1369145 * 2 ^ 59
def prefixEnd_1369145 : Nat := 4983230072969 + 3 ^ 40 * 1369145 * 2
def baseEnd_1369145 : Nat := 234343156900050315863641

theorem tailTrace_1369145 : CollatzResearch.WordTrace tailWord_1369145 prefixEnd_1369145 234343156900050315863641 := by
  unfold tailWord_1369145
  simp only [CollatzResearch.WordTrace]
  refine ⟨49936820624828971194844889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33291213749885980796563259 49936820624828971194844889)
  ·
    refine ⟨37452615468621728396133667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49936820624828971194844889 37452615468621728396133667)
    ·
      refine ⟨56178923202932592594200501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37452615468621728396133667 56178923202932592594200501)
      ·
        refine ⟨5266774050274930555706297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56178923202932592594200501 5266774050274930555706297)
        ·
          refine ⟨3950080537706197916779723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5266774050274930555706297 3950080537706197916779723)
          ·
            refine ⟨5925120806559296875169585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950080537706197916779723 5925120806559296875169585)
            ·
              refine ⟨4443840604919472656377189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5925120806559296875169585 4443840604919472656377189)
              ·
                refine ⟨833220113422401123070723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4443840604919472656377189 833220113422401123070723)
                ·
                  refine ⟨1249830170133601684606085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833220113422401123070723 1249830170133601684606085)
                  ·
                    refine ⟨234343156900050315863641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249830170133601684606085 234343156900050315863641)
                    ·
                      rfl

theorem cell23_1369145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 4].length) (baseStart_1369145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369145 prefixEnd_1369145 := by exact prefixLift 1369145
  have htrace : WordTrace (prefixWord ++ tailWord_1369145) baseStart_1369145 baseEnd_1369145 := by
    simpa [prefixWord, tailWord_1369145, baseEnd_1369145] using wordTrace_append hprefix tailTrace_1369145
  have hstable : (prefixWord ++ tailWord_1369145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369145).length < 2 ^ (prefixWord ++ tailWord_1369145).sum := by decide
  have hdescent : baseEnd_1369145 < baseStart_1369145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369171 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 1, 5]
def baseStart_1369171 : Nat := 118140960795 + 1369171 * 2 ^ 59
def prefixEnd_1369171 : Nat := 4983230072969 + 3 ^ 40 * 1369171 * 2
def baseEnd_1369171 : Nat := 234347607065722615288601

theorem tailTrace_1369171 : CollatzResearch.WordTrace tailWord_1369171 prefixEnd_1369171 234347607065722615288601 := by
  unfold tailWord_1369171
  simp only [CollatzResearch.WordTrace]
  refine ⟨49937768922734777635291367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33291845948489851756860911 49937768922734777635291367)
  ·
    refine ⟨74906653384102166452937051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49937768922734777635291367 74906653384102166452937051)
    ·
      refine ⟨112359980076153249679405577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74906653384102166452937051 112359980076153249679405577)
      ·
        refine ⟨84269985057114937259554183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112359980076153249679405577 84269985057114937259554183)
        ·
          refine ⟨126404977585672405889331275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84269985057114937259554183 126404977585672405889331275)
          ·
            refine ⟨189607466378508608833996913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126404977585672405889331275 189607466378508608833996913)
            ·
              refine ⟨142205599783881456625497685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189607466378508608833996913 142205599783881456625497685)
              ·
                refine ⟨1666471872467360819830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 142205599783881456625497685 1666471872467360819830051)
                ·
                  refine ⟨2499707808701041229745077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666471872467360819830051 2499707808701041229745077)
                  ·
                    refine ⟨234347607065722615288601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2499707808701041229745077 234347607065722615288601)
                    ·
                      rfl

theorem cell23_1369171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 5].length) (baseStart_1369171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369171 prefixEnd_1369171 := by exact prefixLift 1369171
  have htrace : WordTrace (prefixWord ++ tailWord_1369171) baseStart_1369171 baseEnd_1369171 := by
    simpa [prefixWord, tailWord_1369171, baseEnd_1369171] using wordTrace_append hprefix tailTrace_1369171
  have hstable : (prefixWord ++ tailWord_1369171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369171).length < 2 ^ (prefixWord ++ tailWord_1369171).sum := by decide
  have hdescent : baseEnd_1369171 < baseStart_1369171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369225 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_1369225 : Nat := 118140960795 + 1369225 * 2 ^ 59
def prefixEnd_1369225 : Nat := 4983230072969 + 3 ^ 40 * 1369225 * 2
def baseEnd_1369225 : Nat := 703070549152510634590555

theorem tailTrace_1369225 : CollatzResearch.WordTrace tailWord_1369225 prefixEnd_1369225 703070549152510634590555 := by
  unfold tailWord_1369225
  simp only [CollatzResearch.WordTrace]
  refine ⟨49939738464539144857757129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33293158976359429905171419 49939738464539144857757129)
  ·
    refine ⟨37454803848404358643317847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49939738464539144857757129 37454803848404358643317847)
    ·
      refine ⟨56182205772606537964976771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37454803848404358643317847 56182205772606537964976771)
      ·
        refine ⟨84273308658909806947465157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56182205772606537964976771 84273308658909806947465157)
        ·
          refine ⟨15801245373545588802649717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84273308658909806947465157 15801245373545588802649717)
          ·
            refine ⟨1481366753769898950248411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15801245373545588802649717 1481366753769898950248411)
            ·
              refine ⟨2222050130654848425372617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481366753769898950248411 2222050130654848425372617)
              ·
                refine ⟨1666537597991136319029463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222050130654848425372617 1666537597991136319029463)
                ·
                  refine ⟨2499806396986704478544195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666537597991136319029463 2499806396986704478544195)
                  ·
                    refine ⟨3749709595480056717816293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2499806396986704478544195 3749709595480056717816293)
                    ·
                      refine ⟨703070549152510634590555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3749709595480056717816293 703070549152510634590555)
                      ·
                        rfl

theorem cell23_1369225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_1369225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369225 prefixEnd_1369225 := by exact prefixLift 1369225
  have htrace : WordTrace (prefixWord ++ tailWord_1369225) baseStart_1369225 baseEnd_1369225 := by
    simpa [prefixWord, tailWord_1369225, baseEnd_1369225] using wordTrace_append hprefix tailTrace_1369225
  have hstable : (prefixWord ++ tailWord_1369225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369225).length < 2 ^ (prefixWord ++ tailWord_1369225).sum := by decide
  have hdescent : baseEnd_1369225 < baseStart_1369225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369242 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1369242 : Nat := 118140960795 + 1369242 * 2 ^ 59
def prefixEnd_1369242 : Nat := 4983230072969 + 3 ^ 40 * 1369242 * 2
def baseEnd_1369242 : Nat := 703079278323637068077977

theorem tailTrace_1369242 : CollatzResearch.WordTrace tailWord_1369242 prefixEnd_1369242 703079278323637068077977 := by
  unfold tailWord_1369242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12485089626369389190281495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33293572336985037840750653 12485089626369389190281495)
  ·
    refine ⟨18727634439554083785422243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12485089626369389190281495 18727634439554083785422243)
    ·
      refine ⟨28091451659331125678133365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18727634439554083785422243 28091451659331125678133365)
      ·
        refine ⟨2633573593062293032325003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28091451659331125678133365 2633573593062293032325003)
        ·
          refine ⟨3950360389593439548487505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2633573593062293032325003 3950360389593439548487505)
          ·
            refine ⟨2962770292195079661365629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3950360389593439548487505 2962770292195079661365629)
            ·
              refine ⟨1111038859573154873012111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2962770292195079661365629 1111038859573154873012111)
              ·
                refine ⟨1666558289359732309518167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111038859573154873012111 1666558289359732309518167)
                ·
                  refine ⟨2499837434039598464277251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666558289359732309518167 2499837434039598464277251)
                  ·
                    refine ⟨3749756151059397696415877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2499837434039598464277251 3749756151059397696415877)
                    ·
                      refine ⟨703079278323637068077977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3749756151059397696415877 703079278323637068077977)
                      ·
                        rfl

theorem cell23_1369242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1369242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369242 prefixEnd_1369242 := by exact prefixLift 1369242
  have htrace : WordTrace (prefixWord ++ tailWord_1369242) baseStart_1369242 baseEnd_1369242 := by
    simpa [prefixWord, tailWord_1369242, baseEnd_1369242] using wordTrace_append hprefix tailTrace_1369242
  have hstable : (prefixWord ++ tailWord_1369242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369242).length < 2 ^ (prefixWord ++ tailWord_1369242).sum := by decide
  have hdescent : baseEnd_1369242 < baseStart_1369242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369285 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_1369285 : Nat := 118140960795 + 1369285 * 2 ^ 59
def prefixEnd_1369285 : Nat := 4983230072969 + 3 ^ 40 * 1369285 * 2
def baseEnd_1369285 : Nat := 703101357991780399840279

theorem tailTrace_1369285 : CollatzResearch.WordTrace tailWord_1369285 prefixEnd_1369285 703101357991780399840279 := by
  unfold tailWord_1369285
  simp only [CollatzResearch.WordTrace]
  refine ⟨49941926844321775104941309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33294617896214516736627539 49941926844321775104941309)
  ·
    refine ⟨18728222566620665664352991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49941926844321775104941309 18728222566620665664352991)
    ·
      refine ⟨28092333849930998496529487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18728222566620665664352991 28092333849930998496529487)
      ·
        refine ⟨42138500774896497744794231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28092333849930998496529487 42138500774896497744794231)
        ·
          refine ⟨63207751162344746617191347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42138500774896497744794231 63207751162344746617191347)
          ·
            refine ⟨94811626743517119925787021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63207751162344746617191347 94811626743517119925787021)
            ·
              refine ⟨35554360028818919972170133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94811626743517119925787021 35554360028818919972170133)
              ·
                refine ⟨1666610626350886873695475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35554360028818919972170133 1666610626350886873695475)
                ·
                  refine ⟨2499915939526330310543213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666610626350886873695475 2499915939526330310543213)
                  ·
                    refine ⟨937468477322373866453705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2499915939526330310543213 937468477322373866453705)
                    ·
                      refine ⟨703101357991780399840279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937468477322373866453705 703101357991780399840279)
                      ·
                        rfl

theorem cell23_1369285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_1369285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369285 prefixEnd_1369285 := by exact prefixLift 1369285
  have htrace : WordTrace (prefixWord ++ tailWord_1369285) baseStart_1369285 baseEnd_1369285 := by
    simpa [prefixWord, tailWord_1369285, baseEnd_1369285] using wordTrace_append hprefix tailTrace_1369285
  have hstable : (prefixWord ++ tailWord_1369285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369285).length < 2 ^ (prefixWord ++ tailWord_1369285).sum := by decide
  have hdescent : baseEnd_1369285 < baseStart_1369285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369293 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_1369293 : Nat := 118140960795 + 1369293 * 2 ^ 59
def prefixEnd_1369293 : Nat := 4983230072969 + 3 ^ 40 * 1369293 * 2
def baseEnd_1369293 : Nat := 703105465837016368540243

theorem tailTrace_1369293 : CollatzResearch.WordTrace tailWord_1369293 prefixEnd_1369293 703105465837016368540243 := by
  unfold tailWord_1369293
  simp only [CollatzResearch.WordTrace]
  refine ⟨49942218628292792471232533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33294812418861861647488355 49942218628292792471232533)
  ·
    refine ⟨2341041498201224647089025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49942218628292792471232533 2341041498201224647089025)
    ·
      refine ⟨1755781123650918485316769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2341041498201224647089025 1755781123650918485316769)
      ·
        refine ⟨1316835842738188863987577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755781123650918485316769 1316835842738188863987577)
        ·
          refine ⟨987626882053641647990683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1316835842738188863987577 987626882053641647990683)
          ·
            refine ⟨1481440323080462471986025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987626882053641647990683 1481440323080462471986025)
            ·
              refine ⟨1111080242310346853989519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481440323080462471986025 1111080242310346853989519)
              ·
                refine ⟨1666620363465520280984279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111080242310346853989519 1666620363465520280984279)
                ·
                  refine ⟨2499930545198280421476419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666620363465520280984279 2499930545198280421476419)
                  ·
                    refine ⟨3749895817797420632214629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2499930545198280421476419 3749895817797420632214629)
                    ·
                      refine ⟨703105465837016368540243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3749895817797420632214629 703105465837016368540243)
                      ·
                        rfl

theorem cell23_1369293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_1369293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369293 prefixEnd_1369293 := by exact prefixLift 1369293
  have htrace : WordTrace (prefixWord ++ tailWord_1369293) baseStart_1369293 baseEnd_1369293 := by
    simpa [prefixWord, tailWord_1369293, baseEnd_1369293] using wordTrace_append hprefix tailTrace_1369293
  have hstable : (prefixWord ++ tailWord_1369293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369293).length < 2 ^ (prefixWord ++ tailWord_1369293).sum := by decide
  have hdescent : baseEnd_1369293 < baseStart_1369293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369355 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 5]
def baseStart_1369355 : Nat := 118140960795 + 1369355 * 2 ^ 59
def prefixEnd_1369355 : Nat := 4983230072969 + 3 ^ 40 * 1369355 * 2
def baseEnd_1369355 : Nat := 78126366848621680662773

theorem tailTrace_1369355 : CollatzResearch.WordTrace tailWord_1369355 prefixEnd_1369355 78126366848621680662773 := by
  unfold tailWord_1369355
  simp only [CollatzResearch.WordTrace]
  refine ⟨49944479954068177059989519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33296319969378784706659679 49944479954068177059989519)
  ·
    refine ⟨74916719931102265589984279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49944479954068177059989519 74916719931102265589984279)
    ·
      refine ⟨112375079896653398384976419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74916719931102265589984279 112375079896653398384976419)
      ·
        refine ⟨168562619844980097577464629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112375079896653398384976419 168562619844980097577464629)
        ·
          refine ⟨15802745610466884147887309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168562619844980097577464629 15802745610466884147887309)
          ·
            refine ⟨5926029603925081555457741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15802745610466884147887309 5926029603925081555457741)
            ·
              refine ⟨2222261101471905583296653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5926029603925081555457741 2222261101471905583296653)
              ·
                refine ⟨833347913051964593736245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222261101471905583296653 833347913051964593736245)
                ·
                  refine ⟨78126366848621680662773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 833347913051964593736245 78126366848621680662773)
                  ·
                    rfl

theorem cell23_1369355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 5].length) (baseStart_1369355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369355 prefixEnd_1369355 := by exact prefixLift 1369355
  have htrace : WordTrace (prefixWord ++ tailWord_1369355) baseStart_1369355 baseEnd_1369355 := by
    simpa [prefixWord, tailWord_1369355, baseEnd_1369355] using wordTrace_append hprefix tailTrace_1369355
  have hstable : (prefixWord ++ tailWord_1369355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369355).length < 2 ^ (prefixWord ++ tailWord_1369355).sum := by decide
  have hdescent : baseEnd_1369355 < baseStart_1369355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369368 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_1369368 : Nat := 118140960795 + 1369368 * 2 ^ 59
def prefixEnd_1369368 : Nat := 4983230072969 + 3 ^ 40 * 1369368 * 2
def baseEnd_1369368 : Nat := 234381325628701191700799

theorem tailTrace_1369368 : CollatzResearch.WordTrace tailWord_1369368 prefixEnd_1369368 234381325628701191700799 := by
  unfold tailWord_1369368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24972477051510540140106379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33296636068680720186808505 24972477051510540140106379)
  ·
    refine ⟨37458715577265810210159569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24972477051510540140106379 37458715577265810210159569)
    ·
      refine ⟨28094036682949357657619677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37458715577265810210159569 28094036682949357657619677)
      ·
        refine ⟨10535263756106009121607379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28094036682949357657619677 10535263756106009121607379)
        ·
          refine ⟨15802895634159013682411069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10535263756106009121607379 15802895634159013682411069)
          ·
            refine ⟨5926085862809630130904151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15802895634159013682411069 5926085862809630130904151)
            ·
              refine ⟨8889128794214445196356227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926085862809630130904151 8889128794214445196356227)
              ·
                refine ⟨13333693191321667794534341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8889128794214445196356227 13333693191321667794534341)
                ·
                  refine ⟨2500067473372812711475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13333693191321667794534341 2500067473372812711475189)
                  ·
                    refine ⟨234381325628701191700799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2500067473372812711475189 234381325628701191700799)
                    ·
                      rfl

theorem cell23_1369368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_1369368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369368 prefixEnd_1369368 := by exact prefixLift 1369368
  have htrace : WordTrace (prefixWord ++ tailWord_1369368) baseStart_1369368 baseEnd_1369368 := by
    simpa [prefixWord, tailWord_1369368, baseEnd_1369368] using wordTrace_append hprefix tailTrace_1369368
  have hstable : (prefixWord ++ tailWord_1369368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369368).length < 2 ^ (prefixWord ++ tailWord_1369368).sum := by decide
  have hdescent : baseEnd_1369368 < baseStart_1369368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369388 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1369388 : Nat := 118140960795 + 1369388 * 2 ^ 59
def prefixEnd_1369388 : Nat := 4983230072969 + 3 ^ 40 * 1369388 * 2
def baseEnd_1369388 : Nat := 703154246499193496852305

theorem tailTrace_1369388 : CollatzResearch.WordTrace tailWord_1369388 prefixEnd_1369388 703154246499193496852305 := by
  unfold tailWord_1369388
  simp only [CollatzResearch.WordTrace]
  refine ⟨24972841781474311847970409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33297122375299082463960545 24972841781474311847970409)
  ·
    refine ⟨18729631336105733885977807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24972841781474311847970409 18729631336105733885977807)
    ·
      refine ⟨28094447004158600828966711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18729631336105733885977807 28094447004158600828966711)
      ·
        refine ⟨42141670506237901243450067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28094447004158600828966711 42141670506237901243450067)
        ·
          refine ⟨63212505759356851865175101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42141670506237901243450067 63212505759356851865175101)
          ·
            refine ⟨23704689659758819449440663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63212505759356851865175101 23704689659758819449440663)
            ·
              refine ⟨35557034489638229174160995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23704689659758819449440663 35557034489638229174160995)
              ·
                refine ⟨53335551734457343761241493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35557034489638229174160995 53335551734457343761241493)
                ·
                  refine ⟨2500103987552687988808195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53335551734457343761241493 2500103987552687988808195)
                  ·
                    refine ⟨3750155981329031983212293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2500103987552687988808195 3750155981329031983212293)
                    ·
                      refine ⟨703154246499193496852305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3750155981329031983212293 703154246499193496852305)
                      ·
                        rfl

theorem cell23_1369388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1369388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369388 prefixEnd_1369388 := by exact prefixLift 1369388
  have htrace : WordTrace (prefixWord ++ tailWord_1369388) baseStart_1369388 baseEnd_1369388 := by
    simpa [prefixWord, tailWord_1369388, baseEnd_1369388] using wordTrace_append hprefix tailTrace_1369388
  have hstable : (prefixWord ++ tailWord_1369388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369388).length < 2 ^ (prefixWord ++ tailWord_1369388).sum := by decide
  have hdescent : baseEnd_1369388 < baseStart_1369388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369425 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_1369425 : Nat := 118140960795 + 1369425 * 2 ^ 59
def prefixEnd_1369425 : Nat := 4983230072969 + 3 ^ 40 * 1369425 * 2
def baseEnd_1369425 : Nat := 703173245283409852089635

theorem tailTrace_1369425 : CollatzResearch.WordTrace tailWord_1369425 prefixEnd_1369425 703173245283409852089635 := by
  unfold tailWord_1369425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49947033063814579015037729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33298022042543052676691819 49947033063814579015037729)
  ·
    refine ⟨37460274797860934261278297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49947033063814579015037729 37460274797860934261278297)
    ·
      refine ⟨28095206098395700695958723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37460274797860934261278297 28095206098395700695958723)
      ·
        refine ⟨42142809147593551043938085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28095206098395700695958723 42142809147593551043938085)
        ·
          refine ⟨7901776715173790820738391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42142809147593551043938085 7901776715173790820738391)
          ·
            refine ⟨11852665072760686231107587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901776715173790820738391 11852665072760686231107587)
            ·
              refine ⟨17778997609141029346661381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11852665072760686231107587 17778997609141029346661381)
              ·
                refine ⟨3333562051713943002499009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17778997609141029346661381 3333562051713943002499009)
                ·
                  refine ⟨2500171538785457251874257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333562051713943002499009 2500171538785457251874257)
                  ·
                    refine ⟨1875128654089092938905693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2500171538785457251874257 1875128654089092938905693)
                    ·
                      refine ⟨703173245283409852089635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1875128654089092938905693 703173245283409852089635)
                      ·
                        rfl

theorem cell23_1369425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_1369425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369425 prefixEnd_1369425 := by exact prefixLift 1369425
  have htrace : WordTrace (prefixWord ++ tailWord_1369425) baseStart_1369425 baseEnd_1369425 := by
    simpa [prefixWord, tailWord_1369425, baseEnd_1369425] using wordTrace_append hprefix tailTrace_1369425
  have hstable : (prefixWord ++ tailWord_1369425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369425).length < 2 ^ (prefixWord ++ tailWord_1369425).sum := by decide
  have hdescent : baseEnd_1369425 < baseStart_1369425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369432 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 1, 4]
def baseStart_1369432 : Nat := 118140960795 + 1369432 * 2 ^ 59
def prefixEnd_1369432 : Nat := 4983230072969 + 3 ^ 40 * 1369432 * 2
def baseEnd_1369432 : Nat := 234392279882663774900701

theorem tailTrace_1369432 : CollatzResearch.WordTrace tailWord_1369432 prefixEnd_1369432 234392279882663774900701 := by
  unfold tailWord_1369432
  simp only [CollatzResearch.WordTrace]
  refine ⟨24973644187394609605271275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33298192249859479473695033 24973644187394609605271275)
  ·
    refine ⟨37460466281091914407906913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24973644187394609605271275 37460466281091914407906913)
    ·
      refine ⟨28095349710818935805930185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37460466281091914407906913 28095349710818935805930185)
      ·
        refine ⟨21071512283114201854447639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28095349710818935805930185 21071512283114201854447639)
        ·
          refine ⟨31607268424671302781671459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21071512283114201854447639 31607268424671302781671459)
          ·
            refine ⟨47410902637006954172507189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31607268424671302781671459 47410902637006954172507189)
            ·
              refine ⟨4444772122219401953672549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47410902637006954172507189 4444772122219401953672549)
              ·
                refine ⟨833394772916137866313603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4444772122219401953672549 833394772916137866313603)
                ·
                  refine ⟨1250092159374206799470405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833394772916137866313603 1250092159374206799470405)
                  ·
                    refine ⟨234392279882663774900701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1250092159374206799470405 234392279882663774900701)
                    ·
                      rfl

theorem cell23_1369432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_1369432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369432 prefixEnd_1369432 := by exact prefixLift 1369432
  have htrace : WordTrace (prefixWord ++ tailWord_1369432) baseStart_1369432 baseEnd_1369432 := by
    simpa [prefixWord, tailWord_1369432, baseEnd_1369432] using wordTrace_append hprefix tailTrace_1369432
  have hstable : (prefixWord ++ tailWord_1369432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369432).length < 2 ^ (prefixWord ++ tailWord_1369432).sum := by decide
  have hdescent : baseEnd_1369432 < baseStart_1369432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369546 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_1369546 : Nat := 118140960795 + 1369546 * 2 ^ 59
def prefixEnd_1369546 : Nat := 4983230072969 + 3 ^ 40 * 1369546 * 2
def baseEnd_1369546 : Nat := 703235376442603878676579

theorem tailTrace_1369546 : CollatzResearch.WordTrace tailWord_1369546 prefixEnd_1369546 703235376442603878676579 := by
  unfold tailWord_1369546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487861574094054170048123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33300964197584144453461661 12487861574094054170048123)
  ·
    refine ⟨18731792361141081255072185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12487861574094054170048123 18731792361141081255072185)
    ·
      refine ⟨14048844270855810941304139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18731792361141081255072185 14048844270855810941304139)
      ·
        refine ⟨21073266406283716411956209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048844270855810941304139 21073266406283716411956209)
        ·
          refine ⟨15804949804712787308967157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21073266406283716411956209 15804949804712787308967157)
          ·
            refine ⟨1481714044191823810215671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15804949804712787308967157 1481714044191823810215671)
            ·
              refine ⟨2222571066287735715323507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481714044191823810215671 2222571066287735715323507)
              ·
                refine ⟨3333856599431603572985261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222571066287735715323507 3333856599431603572985261)
                ·
                  refine ⟨1250196224786851339869473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3333856599431603572985261 1250196224786851339869473)
                  ·
                    refine ⟨937647168590138504902105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250196224786851339869473 937647168590138504902105)
                    ·
                      refine ⟨703235376442603878676579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937647168590138504902105 703235376442603878676579)
                      ·
                        rfl

theorem cell23_1369546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_1369546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369546 prefixEnd_1369546 := by exact prefixLift 1369546
  have htrace : WordTrace (prefixWord ++ tailWord_1369546) baseStart_1369546 baseEnd_1369546 := by
    simpa [prefixWord, tailWord_1369546, baseEnd_1369546] using wordTrace_append hprefix tailTrace_1369546
  have hstable : (prefixWord ++ tailWord_1369546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369546).length < 2 ^ (prefixWord ++ tailWord_1369546).sum := by decide
  have hdescent : baseEnd_1369546 < baseStart_1369546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369612 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_1369612 : Nat := 118140960795 + 1369612 * 2 ^ 59
def prefixEnd_1369612 : Nat := 4983230072969 + 3 ^ 40 * 1369612 * 2
def baseEnd_1369612 : Nat := 234423088721933540150425

theorem tailTrace_1369612 : CollatzResearch.WordTrace tailWord_1369612 prefixEnd_1369612 234423088721933540150425 := by
  unfold tailWord_1369612
  simp only [CollatzResearch.WordTrace]
  refine ⟨24976926757068554976047545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33302569009424739968063393 24976926757068554976047545)
  ·
    refine ⟨18732695067801416232035659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24976926757068554976047545 18732695067801416232035659)
    ·
      refine ⟨28099042601702124348053489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18732695067801416232035659 28099042601702124348053489)
      ·
        refine ⟨21074281951276593261040117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28099042601702124348053489 21074281951276593261040117)
        ·
          refine ⟨1975713932932180618222511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21074281951276593261040117 1975713932932180618222511)
          ·
            refine ⟨2963570899398270927333767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975713932932180618222511 2963570899398270927333767)
            ·
              refine ⟨4445356349097406391000651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2963570899398270927333767 4445356349097406391000651)
              ·
                refine ⟨6668034523646109586500977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445356349097406391000651 6668034523646109586500977)
                ·
                  refine ⟨5001025892734582189875733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6668034523646109586500977 5001025892734582189875733)
                  ·
                    refine ⟨234423088721933540150425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5001025892734582189875733 234423088721933540150425)
                    ·
                      rfl

theorem cell23_1369612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_1369612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369612 prefixEnd_1369612 := by exact prefixLift 1369612
  have htrace : WordTrace (prefixWord ++ tailWord_1369612) baseStart_1369612 baseEnd_1369612 := by
    simpa [prefixWord, tailWord_1369612, baseEnd_1369612] using wordTrace_append hprefix tailTrace_1369612
  have hstable : (prefixWord ++ tailWord_1369612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369612).length < 2 ^ (prefixWord ++ tailWord_1369612).sum := by decide
  have hdescent : baseEnd_1369612 < baseStart_1369612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369613 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1369613 : Nat := 118140960795 + 1369613 * 2 ^ 59
def prefixEnd_1369613 : Nat := 4983230072969 + 3 ^ 40 * 1369613 * 2
def baseEnd_1369613 : Nat := 703269779646455116538771

theorem tailTrace_1369613 : CollatzResearch.WordTrace tailWord_1369613 prefixEnd_1369613 703269779646455116538771 := by
  unfold tailWord_1369613
  simp only [CollatzResearch.WordTrace]
  refine ⟨49953889987133487122881493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33302593324755658081920995 49953889987133487122881493)
  ·
    refine ⟨1170794296573441104442535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49953889987133487122881493 1170794296573441104442535)
    ·
      refine ⟨1756191444860161656663803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170794296573441104442535 1756191444860161656663803)
      ·
        refine ⟨2634287167290242484995705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1756191444860161656663803 2634287167290242484995705)
        ·
          refine ⟨1975715375467681863746779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2634287167290242484995705 1975715375467681863746779)
          ·
            refine ⟨2963573063201522795620169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975715375467681863746779 2963573063201522795620169)
            ·
              refine ⟨2222679797401142096715127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963573063201522795620169 2222679797401142096715127)
              ·
                refine ⟨3334019696101713145072691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222679797401142096715127 3334019696101713145072691)
                ·
                  refine ⟨5001029544152569717609037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334019696101713145072691 5001029544152569717609037)
                  ·
                    refine ⟨1875386079057213644103389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5001029544152569717609037 1875386079057213644103389)
                    ·
                      refine ⟨703269779646455116538771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1875386079057213644103389 703269779646455116538771)
                      ·
                        rfl

theorem cell23_1369613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1369613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369613 prefixEnd_1369613 := by exact prefixLift 1369613
  have htrace : WordTrace (prefixWord ++ tailWord_1369613) baseStart_1369613 baseEnd_1369613 := by
    simpa [prefixWord, tailWord_1369613, baseEnd_1369613] using wordTrace_append hprefix tailTrace_1369613
  have hstable : (prefixWord ++ tailWord_1369613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369613).length < 2 ^ (prefixWord ++ tailWord_1369613).sum := by decide
  have hdescent : baseEnd_1369613 < baseStart_1369613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369619 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 1, 4, 2]
def baseStart_1369619 : Nat := 118140960795 + 1369619 * 2 ^ 59
def prefixEnd_1369619 : Nat := 4983230072969 + 3 ^ 40 * 1369619 * 2
def baseEnd_1369619 : Nat := 703272860530382093063743

theorem tailTrace_1369619 : CollatzResearch.WordTrace tailWord_1369619 prefixEnd_1369619 703272860530382093063743 := by
  unfold tailWord_1369619
  simp only [CollatzResearch.WordTrace]
  refine ⟨49954108825111750147599911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33302739216741166765066607 49954108825111750147599911)
  ·
    refine ⟨74931163237667625221399867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49954108825111750147599911 74931163237667625221399867)
    ·
      refine ⟨112396744856501437832099801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74931163237667625221399867 112396744856501437832099801)
      ·
        refine ⟨84297558642376078374074851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112396744856501437832099801 84297558642376078374074851)
        ·
          refine ⟨126446337963564117561112277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84297558642376078374074851 126446337963564117561112277)
          ·
            refine ⟨2963586046021034005338569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 126446337963564117561112277 2963586046021034005338569)
            ·
              refine ⟨2222689534515775504003927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963586046021034005338569 2222689534515775504003927)
              ·
                refine ⟨3334034301773663256005891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222689534515775504003927 3334034301773663256005891)
                ·
                  refine ⟨5001051452660494884008837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334034301773663256005891 5001051452660494884008837)
                  ·
                    refine ⟨937697147373842790751657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001051452660494884008837 937697147373842790751657)
                    ·
                      refine ⟨703272860530382093063743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937697147373842790751657 703272860530382093063743)
                      ·
                        rfl

theorem cell23_1369619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4, 2].length) (baseStart_1369619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369619 prefixEnd_1369619 := by exact prefixLift 1369619
  have htrace : WordTrace (prefixWord ++ tailWord_1369619) baseStart_1369619 baseEnd_1369619 := by
    simpa [prefixWord, tailWord_1369619, baseEnd_1369619] using wordTrace_append hprefix tailTrace_1369619
  have hstable : (prefixWord ++ tailWord_1369619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369619).length < 2 ^ (prefixWord ++ tailWord_1369619).sum := by decide
  have hdescent : baseEnd_1369619 < baseStart_1369619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369640 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1369640 : Nat := 118140960795 + 1369640 * 2 ^ 59
def prefixEnd_1369640 : Nat := 4983230072969 + 3 ^ 40 * 1369640 * 2
def baseEnd_1369640 : Nat := 703283643624126510901147

theorem tailTrace_1369640 : CollatzResearch.WordTrace tailWord_1369640 prefixEnd_1369640 703283643624126510901147 := by
  unfold tailWord_1369640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977437379017835367057187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33303249838690447156076249 24977437379017835367057187)
  ·
    refine ⟨37466156068526753050585781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24977437379017835367057187 37466156068526753050585781)
    ·
      refine ⟨3512452131424383098492417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37466156068526753050585781 3512452131424383098492417)
      ·
        refine ⟨2634339098568287323869313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3512452131424383098492417 2634339098568287323869313)
        ·
          refine ⟨1975754323926215492901985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2634339098568287323869313 1975754323926215492901985)
          ·
            refine ⟨1481815742944661619676489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975754323926215492901985 1481815742944661619676489)
            ·
              refine ⟨1111361807208496214757367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481815742944661619676489 1111361807208496214757367)
              ·
                refine ⟨1667042710812744322136051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111361807208496214757367 1667042710812744322136051)
                ·
                  refine ⟨2500564066219116483204077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667042710812744322136051 2500564066219116483204077)
                  ·
                    refine ⟨937711524832168681201529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2500564066219116483204077 937711524832168681201529)
                    ·
                      refine ⟨703283643624126510901147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937711524832168681201529 703283643624126510901147)
                      ·
                        rfl

theorem cell23_1369640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1369640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369640 prefixEnd_1369640 := by exact prefixLift 1369640
  have htrace : WordTrace (prefixWord ++ tailWord_1369640) baseStart_1369640 baseEnd_1369640 := by
    simpa [prefixWord, tailWord_1369640, baseEnd_1369640] using wordTrace_append hprefix tailTrace_1369640
  have hstable : (prefixWord ++ tailWord_1369640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369640).length < 2 ^ (prefixWord ++ tailWord_1369640).sum := by decide
  have hdescent : baseEnd_1369640 < baseStart_1369640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369653 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_1369653 : Nat := 118140960795 + 1369653 * 2 ^ 59
def prefixEnd_1369653 : Nat := 4983230072969 + 3 ^ 40 * 1369653 * 2
def baseEnd_1369653 : Nat := 703290318872634960038587

theorem tailTrace_1369653 : CollatzResearch.WordTrace tailWord_1369653 prefixEnd_1369653 703290318872634960038587 := by
  unfold tailWord_1369653
  simp only [CollatzResearch.WordTrace]
  refine ⟨49955348906988573954337613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33303565937992382636225075 49955348906988573954337613)
  ·
    refine ⟨18733255840120715232876605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49955348906988573954337613 18733255840120715232876605)
    ·
      refine ⟨7024970940045268212328727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18733255840120715232876605 7024970940045268212328727)
      ·
        refine ⟨10537456410067902318493091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7024970940045268212328727 10537456410067902318493091)
        ·
          refine ⟨15806184615101853477739637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10537456410067902318493091 15806184615101853477739637)
          ·
            refine ⟨1481829807665798763538091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15806184615101853477739637 1481829807665798763538091)
            ·
              refine ⟨2222744711498698145307137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481829807665798763538091 2222744711498698145307137)
              ·
                refine ⟨1667058533624023608980353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222744711498698145307137 1667058533624023608980353)
                ·
                  refine ⟨1250293900218017706735265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667058533624023608980353 1250293900218017706735265)
                  ·
                    refine ⟨937720425163513280051449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250293900218017706735265 937720425163513280051449)
                    ·
                      refine ⟨703290318872634960038587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937720425163513280051449 703290318872634960038587)
                      ·
                        rfl

theorem cell23_1369653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_1369653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369653 prefixEnd_1369653 := by exact prefixLift 1369653
  have htrace : WordTrace (prefixWord ++ tailWord_1369653) baseStart_1369653 baseEnd_1369653 := by
    simpa [prefixWord, tailWord_1369653, baseEnd_1369653] using wordTrace_append hprefix tailTrace_1369653
  have hstable : (prefixWord ++ tailWord_1369653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369653).length < 2 ^ (prefixWord ++ tailWord_1369653).sum := by decide
  have hdescent : baseEnd_1369653 < baseStart_1369653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369670 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1369670 : Nat := 118140960795 + 1369670 * 2 ^ 59
def prefixEnd_1369670 : Nat := 4983230072969 + 3 ^ 40 * 1369670 * 2
def baseEnd_1369670 : Nat := 703299048043761393526009

theorem tailTrace_1369670 : CollatzResearch.WordTrace tailWord_1369670 prefixEnd_1369670 703299048043761393526009 := by
  unfold tailWord_1369670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561124029622718308053327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33303979298617990571804309 1561124029622718308053327)
  ·
    refine ⟨2341686044434077462079991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1561124029622718308053327 2341686044434077462079991)
    ·
      refine ⟨3512529066651116193119987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341686044434077462079991 3512529066651116193119987)
      ·
        refine ⟨5268793599976674289679981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512529066651116193119987 5268793599976674289679981)
        ·
          refine ⟨1975797599991252858629993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5268793599976674289679981 1975797599991252858629993)
          ·
            refine ⟨1481848199993439643972495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975797599991252858629993 1481848199993439643972495)
            ·
              refine ⟨2222772299990159465958743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481848199993439643972495 2222772299990159465958743)
              ·
                refine ⟨3334158449985239198938115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222772299990159465958743 3334158449985239198938115)
                ·
                  refine ⟨5001237674977858798407173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334158449985239198938115 5001237674977858798407173)
                  ·
                    refine ⟨937732064058348524701345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001237674977858798407173 937732064058348524701345)
                    ·
                      refine ⟨703299048043761393526009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937732064058348524701345 703299048043761393526009)
                      ·
                        rfl

theorem cell23_1369670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1369670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369670 prefixEnd_1369670 := by exact prefixLift 1369670
  have htrace : WordTrace (prefixWord ++ tailWord_1369670) baseStart_1369670 baseEnd_1369670 := by
    simpa [prefixWord, tailWord_1369670, baseEnd_1369670] using wordTrace_append hprefix tailTrace_1369670
  have hstable : (prefixWord ++ tailWord_1369670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369670).length < 2 ^ (prefixWord ++ tailWord_1369670).sum := by decide
  have hdescent : baseEnd_1369670 < baseStart_1369670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369685 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1369685 : Nat := 118140960795 + 1369685 * 2 ^ 59
def prefixEnd_1369685 : Nat := 4983230072969 + 3 ^ 40 * 1369685 * 2
def baseEnd_1369685 : Nat := 234435583417859611612813

theorem tailTrace_1369685 : CollatzResearch.WordTrace tailWord_1369685 prefixEnd_1369685 234435583417859611612813 := by
  unfold tailWord_1369685
  simp only [CollatzResearch.WordTrace]
  refine ⟨49956516042872643419502509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33304344028581762279668339 49956516042872643419502509)
  ·
    refine ⟨18733693516077241282313441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49956516042872643419502509 18733693516077241282313441)
    ·
      refine ⟨14050270137057930961735081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18733693516077241282313441 14050270137057930961735081)
      ·
        refine ⟨10537702602793448221301311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14050270137057930961735081 10537702602793448221301311)
        ·
          refine ⟨15806553904190172331951967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10537702602793448221301311 15806553904190172331951967)
          ·
            refine ⟨23709830856285258497927951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15806553904190172331951967 23709830856285258497927951)
            ·
              refine ⟨35564746284427887746891927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23709830856285258497927951 35564746284427887746891927)
              ·
                refine ⟨53347119426641831620337891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35564746284427887746891927 53347119426641831620337891)
                ·
                  refine ⟨80020679139962747430506837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53347119426641831620337891 80020679139962747430506837)
                  ·
                    refine ⟨234435583417859611612813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 80020679139962747430506837 234435583417859611612813)
                    ·
                      rfl

theorem cell23_1369685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1369685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369685 prefixEnd_1369685 := by exact prefixLift 1369685
  have htrace : WordTrace (prefixWord ++ tailWord_1369685) baseStart_1369685 baseEnd_1369685 := by
    simpa [prefixWord, tailWord_1369685, baseEnd_1369685] using wordTrace_append hprefix tailTrace_1369685
  have hstable : (prefixWord ++ tailWord_1369685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369685).length < 2 ^ (prefixWord ++ tailWord_1369685).sum := by decide
  have hdescent : baseEnd_1369685 < baseStart_1369685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369695 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1369695 : Nat := 118140960795 + 1369695 * 2 ^ 59
def prefixEnd_1369695 : Nat := 4983230072969 + 3 ^ 40 * 1369695 * 2
def baseEnd_1369695 : Nat := 703311885060123795713393

theorem tailTrace_1369695 : CollatzResearch.WordTrace tailWord_1369695 prefixEnd_1369695 703311885060123795713393 := by
  unfold tailWord_1369695
  simp only [CollatzResearch.WordTrace]
  refine ⟨49956880772836415127366539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33304587181890943418244359 49956880772836415127366539)
  ·
    refine ⟨74935321159254622691049809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49956880772836415127366539 74935321159254622691049809)
    ·
      refine ⟨56201490869440967018287357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74935321159254622691049809 56201490869440967018287357)
      ·
        refine ⟨21075559076040362631857759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56201490869440967018287357 21075559076040362631857759)
        ·
          refine ⟨31613338614060543947786639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21075559076040362631857759 31613338614060543947786639)
          ·
            refine ⟨47420007921090815921679959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31613338614060543947786639 47420007921090815921679959)
            ·
              refine ⟨71130011881636223882519939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47420007921090815921679959 71130011881636223882519939)
              ·
                refine ⟨106695017822454335823779909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71130011881636223882519939 106695017822454335823779909)
                ·
                  refine ⟨20005315841710187966958733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106695017822454335823779909 20005315841710187966958733)
                  ·
                    refine ⟨7501993440641320487609525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20005315841710187966958733 7501993440641320487609525)
                    ·
                      refine ⟨703311885060123795713393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7501993440641320487609525 703311885060123795713393)
                      ·
                        rfl

theorem cell23_1369695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1369695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369695 prefixEnd_1369695 := by exact prefixLift 1369695
  have htrace : WordTrace (prefixWord ++ tailWord_1369695) baseStart_1369695 baseEnd_1369695 := by
    simpa [prefixWord, tailWord_1369695, baseEnd_1369695] using wordTrace_append hprefix tailTrace_1369695
  have hstable : (prefixWord ++ tailWord_1369695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369695).length < 2 ^ (prefixWord ++ tailWord_1369695).sum := by decide
  have hdescent : baseEnd_1369695 < baseStart_1369695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369705 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_1369705 : Nat := 118140960795 + 1369705 * 2 ^ 59
def prefixEnd_1369705 : Nat := 4983230072969 + 3 ^ 40 * 1369705 * 2
def baseEnd_1369705 : Nat := 703317019866668756588347

theorem tailTrace_1369705 : CollatzResearch.WordTrace tailWord_1369705 prefixEnd_1369705 703317019866668756588347 := by
  unfold tailWord_1369705
  simp only [CollatzResearch.WordTrace]
  refine ⟨49957245502800186835230569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33304830335200124556820379 49957245502800186835230569)
  ·
    refine ⟨37467934127100140126422927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49957245502800186835230569 37467934127100140126422927)
    ·
      refine ⟨56201901190650210189634391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37467934127100140126422927 56201901190650210189634391)
      ·
        refine ⟨84302851785975315284451587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56201901190650210189634391 84302851785975315284451587)
        ·
          refine ⟨126454277678962972926677381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84302851785975315284451587 126454277678962972926677381)
          ·
            refine ⟨23710177064805557423752009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126454277678962972926677381 23710177064805557423752009)
            ·
              refine ⟨17782632798604168067814007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23710177064805557423752009 17782632798604168067814007)
              ·
                refine ⟨26673949197906252101721011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17782632798604168067814007 26673949197906252101721011)
                ·
                  refine ⟨40010923796859378152581517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26673949197906252101721011 40010923796859378152581517)
                  ·
                    refine ⟨15004096423822266807218069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40010923796859378152581517 15004096423822266807218069)
                    ·
                      refine ⟨703317019866668756588347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15004096423822266807218069 703317019866668756588347)
                      ·
                        rfl

theorem cell23_1369705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_1369705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369705 prefixEnd_1369705 := by exact prefixLift 1369705
  have htrace : WordTrace (prefixWord ++ tailWord_1369705) baseStart_1369705 baseEnd_1369705 := by
    simpa [prefixWord, tailWord_1369705, baseEnd_1369705] using wordTrace_append hprefix tailTrace_1369705
  have hstable : (prefixWord ++ tailWord_1369705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369705).length < 2 ^ (prefixWord ++ tailWord_1369705).sum := by decide
  have hdescent : baseEnd_1369705 < baseStart_1369705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369799 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_1369799 : Nat := 118140960795 + 1369799 * 2 ^ 59
def prefixEnd_1369799 : Nat := 4983230072969 + 3 ^ 40 * 1369799 * 2
def baseEnd_1369799 : Nat := 703365287048191388812915

theorem tailTrace_1369799 : CollatzResearch.WordTrace tailWord_1369799 prefixEnd_1369799 703365287048191388812915 := by
  unfold tailWord_1369799
  simp only [CollatzResearch.WordTrace]
  refine ⟨49960673964459640889152451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33307115976306427259434967 49960673964459640889152451)
  ·
    refine ⟨74941010946689461333728677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49960673964459640889152451 74941010946689461333728677)
    ·
      refine ⟨14051439552504274000074127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74941010946689461333728677 14051439552504274000074127)
      ·
        refine ⟨21077159328756411000111191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14051439552504274000074127 21077159328756411000111191)
        ·
          refine ⟨31615738993134616500166787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21077159328756411000111191 31615738993134616500166787)
          ·
            refine ⟨47423608489701924750250181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31615738993134616500166787 47423608489701924750250181)
            ·
              refine ⟨8891926591819110890671909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47423608489701924750250181 8891926591819110890671909)
              ·
                refine ⟨1667236235966083292000983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8891926591819110890671909 1667236235966083292000983)
                ·
                  refine ⟨2500854353949124938001475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667236235966083292000983 2500854353949124938001475)
                  ·
                    refine ⟨3751281530923687407002213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2500854353949124938001475 3751281530923687407002213)
                    ·
                      refine ⟨703365287048191388812915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3751281530923687407002213 703365287048191388812915)
                      ·
                        rfl

theorem cell23_1369799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_1369799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369799 prefixEnd_1369799 := by exact prefixLift 1369799
  have htrace : WordTrace (prefixWord ++ tailWord_1369799) baseStart_1369799 baseEnd_1369799 := by
    simpa [prefixWord, tailWord_1369799, baseEnd_1369799] using wordTrace_append hprefix tailTrace_1369799
  have hstable : (prefixWord ++ tailWord_1369799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369799).length < 2 ^ (prefixWord ++ tailWord_1369799).sum := by decide
  have hdescent : baseEnd_1369799 < baseStart_1369799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369810 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1369810 : Nat := 118140960795 + 1369810 * 2 ^ 59
def prefixEnd_1369810 : Nat := 4983230072969 + 3 ^ 40 * 1369810 * 2
def baseEnd_1369810 : Nat := 703370935335390845775365

theorem tailTrace_1369810 : CollatzResearch.WordTrace tailWord_1369810 prefixEnd_1369810 703370935335390845775365 := by
  unfold tailWord_1369810
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490268791854947441950721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33307383444946526511868589 12490268791854947441950721)
  ·
    refine ⟨9367701593891210581463041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12490268791854947441950721 9367701593891210581463041)
    ·
      refine ⟨7025776195418407936097281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9367701593891210581463041 7025776195418407936097281)
      ·
        refine ⟨5269332146563805952072961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7025776195418407936097281 5269332146563805952072961)
        ·
          refine ⟨3951999109922854464054721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5269332146563805952072961 3951999109922854464054721)
          ·
            refine ⟨2963999332442140848041041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3951999109922854464054721 2963999332442140848041041)
            ·
              refine ⟨2222999499331605636030781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2963999332442140848041041 2222999499331605636030781)
              ·
                refine ⟨833624812249352113511543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222999499331605636030781 833624812249352113511543)
                ·
                  refine ⟨1250437218374028170267315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833624812249352113511543 1250437218374028170267315)
                  ·
                    refine ⟨1875655827561042255400973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1250437218374028170267315 1875655827561042255400973)
                    ·
                      refine ⟨703370935335390845775365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1875655827561042255400973 703370935335390845775365)
                      ·
                        rfl

theorem cell23_1369810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1369810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369810 prefixEnd_1369810 := by exact prefixLift 1369810
  have htrace : WordTrace (prefixWord ++ tailWord_1369810) baseStart_1369810 baseEnd_1369810 := by
    simpa [prefixWord, tailWord_1369810, baseEnd_1369810] using wordTrace_append hprefix tailTrace_1369810
  have hstable : (prefixWord ++ tailWord_1369810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369810).length < 2 ^ (prefixWord ++ tailWord_1369810).sum := by decide
  have hdescent : baseEnd_1369810 < baseStart_1369810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369816 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_1369816 : Nat := 118140960795 + 1369816 * 2 ^ 59
def prefixEnd_1369816 : Nat := 4983230072969 + 3 ^ 40 * 1369816 * 2
def baseEnd_1369816 : Nat := 703374016219317822300337

theorem tailTrace_1369816 : CollatzResearch.WordTrace tailWord_1369816 prefixEnd_1369816 703374016219317822300337 := by
  unfold tailWord_1369816
  simp only [CollatzResearch.WordTrace]
  refine ⟨24980647002699026396260651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33307529336932035195014201 24980647002699026396260651)
  ·
    refine ⟨37470970504048539594390977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24980647002699026396260651 37470970504048539594390977)
    ·
      refine ⟨28103227878036404695793233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37470970504048539594390977 28103227878036404695793233)
      ·
        refine ⟨21077420908527303521844925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28103227878036404695793233 21077420908527303521844925)
        ·
          refine ⟨7904032840697738820691847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21077420908527303521844925 7904032840697738820691847)
          ·
            refine ⟨11856049261046608231037771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904032840697738820691847 11856049261046608231037771)
            ·
              refine ⟨17784073891569912346556657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11856049261046608231037771 17784073891569912346556657)
              ·
                refine ⟨13338055418677434259917493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17784073891569912346556657 13338055418677434259917493)
                ·
                  refine ⟨1250442695501009461867265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13338055418677434259917493 1250442695501009461867265)
                  ·
                    refine ⟨937832021625757096400449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250442695501009461867265 937832021625757096400449)
                    ·
                      refine ⟨703374016219317822300337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937832021625757096400449 703374016219317822300337)
                      ·
                        rfl

theorem cell23_1369816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_1369816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369816 prefixEnd_1369816 := by exact prefixLift 1369816
  have htrace : WordTrace (prefixWord ++ tailWord_1369816) baseStart_1369816 baseEnd_1369816 := by
    simpa [prefixWord, tailWord_1369816, baseEnd_1369816] using wordTrace_append hprefix tailTrace_1369816
  have hstable : (prefixWord ++ tailWord_1369816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369816).length < 2 ^ (prefixWord ++ tailWord_1369816).sum := by decide
  have hdescent : baseEnd_1369816 < baseStart_1369816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369846 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1369846 : Nat := 118140960795 + 1369846 * 2 ^ 59
def prefixEnd_1369846 : Nat := 4983230072969 + 3 ^ 40 * 1369846 * 2
def baseEnd_1369846 : Nat := 703389420638952704925199

theorem tailTrace_1369846 : CollatzResearch.WordTrace tailWord_1369846 prefixEnd_1369846 703389420638952704925199 := by
  unfold tailWord_1369846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122649262205585494757087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33308258796859578610742261 3122649262205585494757087)
  ·
    refine ⟨4683973893308378242135631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122649262205585494757087 4683973893308378242135631)
    ·
      refine ⟨7025960839962567363203447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4683973893308378242135631 7025960839962567363203447)
      ·
        refine ⟨10538941259943851044805171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7025960839962567363203447 10538941259943851044805171)
        ·
          refine ⟨15808411889915776567207757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10538941259943851044805171 15808411889915776567207757)
          ·
            refine ⟨5928154458718416212702909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15808411889915776567207757 5928154458718416212702909)
            ·
              refine ⟨2223057922019406079763591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5928154458718416212702909 2223057922019406079763591)
              ·
                refine ⟨3334586883029109119645387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223057922019406079763591 3334586883029109119645387)
                ·
                  refine ⟨5001880324543663679468081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334586883029109119645387 5001880324543663679468081)
                  ·
                    refine ⟨3751410243407747759601061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5001880324543663679468081 3751410243407747759601061)
                    ·
                      refine ⟨703389420638952704925199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3751410243407747759601061 703389420638952704925199)
                      ·
                        rfl

theorem cell23_1369846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1369846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369846 prefixEnd_1369846 := by exact prefixLift 1369846
  have htrace : WordTrace (prefixWord ++ tailWord_1369846) baseStart_1369846 baseEnd_1369846 := by
    simpa [prefixWord, tailWord_1369846, baseEnd_1369846] using wordTrace_append hprefix tailTrace_1369846
  have hstable : (prefixWord ++ tailWord_1369846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369846).length < 2 ^ (prefixWord ++ tailWord_1369846).sum := by decide
  have hdescent : baseEnd_1369846 < baseStart_1369846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369866 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1369866 : Nat := 118140960795 + 1369866 * 2 ^ 59
def prefixEnd_1369866 : Nat := 4983230072969 + 3 ^ 40 * 1369866 * 2
def baseEnd_1369866 : Nat := 703399690252042626675107

theorem tailTrace_1369866 : CollatzResearch.WordTrace tailWord_1369866 prefixEnd_1369866 703399690252042626675107 := by
  unfold tailWord_1369866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490779413804227832960363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33308745103477940887894301 12490779413804227832960363)
  ·
    refine ⟨18736169120706341749440545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12490779413804227832960363 18736169120706341749440545)
    ·
      refine ⟨14052126840529756312080409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18736169120706341749440545 14052126840529756312080409)
      ·
        refine ⟨10539095130397317234060307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14052126840529756312080409 10539095130397317234060307)
        ·
          refine ⟨15808642695595975851090461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10539095130397317234060307 15808642695595975851090461)
          ·
            refine ⟨5928241010848490944158923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15808642695595975851090461 5928241010848490944158923)
            ·
              refine ⟨8892361516272736416238385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928241010848490944158923 8892361516272736416238385)
              ·
                refine ⟨6669271137204552312178789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8892361516272736416238385 6669271137204552312178789)
                ·
                  refine ⟨1250488338225853558533523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6669271137204552312178789 1250488338225853558533523)
                  ·
                    refine ⟨1875732507338780337800285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1250488338225853558533523 1875732507338780337800285)
                    ·
                      refine ⟨703399690252042626675107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1875732507338780337800285 703399690252042626675107)
                      ·
                        rfl

theorem cell23_1369866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1369866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369866 prefixEnd_1369866 := by exact prefixLift 1369866
  have htrace : WordTrace (prefixWord ++ tailWord_1369866) baseStart_1369866 baseEnd_1369866 := by
    simpa [prefixWord, tailWord_1369866, baseEnd_1369866] using wordTrace_append hprefix tailTrace_1369866
  have hstable : (prefixWord ++ tailWord_1369866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369866).length < 2 ^ (prefixWord ++ tailWord_1369866).sum := by decide
  have hdescent : baseEnd_1369866 < baseStart_1369866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369900 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 3]
def baseStart_1369900 : Nat := 118140960795 + 1369900 * 2 ^ 59
def prefixEnd_1369900 : Nat := 4983230072969 + 3 ^ 40 * 1369900 * 2
def baseEnd_1369900 : Nat := 703417148594295493649951

theorem tailTrace_1369900 : CollatzResearch.WordTrace tailWord_1369900 prefixEnd_1369900 703417148594295493649951 := by
  unfold tailWord_1369900
  simp only [CollatzResearch.WordTrace]
  refine ⟨24982178868546867569289577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33309571824729156759052769 24982178868546867569289577)
  ·
    refine ⟨18736634151410150676967183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24982178868546867569289577 18736634151410150676967183)
    ·
      refine ⟨28104951227115226015450775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18736634151410150676967183 28104951227115226015450775)
      ·
        refine ⟨42157426840672839023176163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28104951227115226015450775 42157426840672839023176163)
        ·
          refine ⟨63236140261009258534764245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42157426840672839023176163 63236140261009258534764245)
          ·
            refine ⟨1482097037367404496908537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 63236140261009258534764245 1482097037367404496908537)
            ·
              refine ⟨1111572778025553372681403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1482097037367404496908537 1111572778025553372681403)
              ·
                refine ⟨1667359167038330059022105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111572778025553372681403 1667359167038330059022105)
                ·
                  refine ⟨1250519375278747544266579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667359167038330059022105 1250519375278747544266579)
                  ·
                    refine ⟨1875779062918121316399869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1250519375278747544266579 1875779062918121316399869)
                    ·
                      refine ⟨703417148594295493649951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1875779062918121316399869 703417148594295493649951)
                      ·
                        rfl

theorem cell23_1369900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_1369900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369900 prefixEnd_1369900 := by exact prefixLift 1369900
  have htrace : WordTrace (prefixWord ++ tailWord_1369900) baseStart_1369900 baseEnd_1369900 := by
    simpa [prefixWord, tailWord_1369900, baseEnd_1369900] using wordTrace_append hprefix tailTrace_1369900
  have hstable : (prefixWord ++ tailWord_1369900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369900).length < 2 ^ (prefixWord ++ tailWord_1369900).sum := by decide
  have hdescent : baseEnd_1369900 < baseStart_1369900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369910 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1369910 : Nat := 118140960795 + 1369910 * 2 ^ 59
def prefixEnd_1369910 : Nat := 4983230072969 + 3 ^ 40 * 1369910 * 2
def baseEnd_1369910 : Nat := 703422283400840454524905

theorem tailTrace_1369910 : CollatzResearch.WordTrace tailWord_1369910 prefixEnd_1369910 703422283400840454524905 := by
  unfold tailWord_1369910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122795154191094177902699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33309814978038337897628789 3122795154191094177902699)
  ·
    refine ⟨4684192731286641266854049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122795154191094177902699 4684192731286641266854049)
    ·
      refine ⟨3513144548464980950140537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4684192731286641266854049 3513144548464980950140537)
      ·
        refine ⟨2634858411348735712605403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3513144548464980950140537 2634858411348735712605403)
        ·
          refine ⟨3952287617023103568908105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634858411348735712605403 3952287617023103568908105)
          ·
            refine ⟨2964215712767327676681079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3952287617023103568908105 2964215712767327676681079)
            ·
              refine ⟨4446323569150991515021619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964215712767327676681079 4446323569150991515021619)
              ·
                refine ⟨6669485353726487272532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446323569150991515021619 6669485353726487272532429)
                ·
                  refine ⟨2501057007647432727199661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6669485353726487272532429 2501057007647432727199661)
                  ·
                    refine ⟨937896377867787272699873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501057007647432727199661 937896377867787272699873)
                    ·
                      refine ⟨703422283400840454524905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937896377867787272699873 703422283400840454524905)
                      ·
                        rfl

theorem cell23_1369910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1369910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369910 prefixEnd_1369910 := by exact prefixLift 1369910
  have htrace : WordTrace (prefixWord ++ tailWord_1369910) baseStart_1369910 baseEnd_1369910 := by
    simpa [prefixWord, tailWord_1369910, baseEnd_1369910] using wordTrace_append hprefix tailTrace_1369910
  have hstable : (prefixWord ++ tailWord_1369910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369910).length < 2 ^ (prefixWord ++ tailWord_1369910).sum := by decide
  have hdescent : baseEnd_1369910 < baseStart_1369910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369940 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_1369940 : Nat := 118140960795 + 1369940 * 2 ^ 59
def prefixEnd_1369940 : Nat := 4983230072969 + 3 ^ 40 * 1369940 * 2
def baseEnd_1369940 : Nat := 703437687820475337149767

theorem tailTrace_1369940 : CollatzResearch.WordTrace tailWord_1369940 prefixEnd_1369940 703437687820475337149767 := by
  unfold tailWord_1369940
  simp only [CollatzResearch.WordTrace]
  refine ⟨24982908328474410985017637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33310544437965881313356849 24982908328474410985017637)
  ·
    refine ⟨4684295311588952059690807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24982908328474410985017637 4684295311588952059690807)
    ·
      refine ⟨7026442967383428089536211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684295311588952059690807 7026442967383428089536211)
      ·
        refine ⟨10539664451075142134304317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7026442967383428089536211 10539664451075142134304317)
        ·
          refine ⟨3952374169153178300364119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10539664451075142134304317 3952374169153178300364119)
          ·
            refine ⟨5928561253729767450546179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952374169153178300364119 5928561253729767450546179)
            ·
              refine ⟨8892841880594651175819269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928561253729767450546179 8892841880594651175819269)
              ·
                refine ⟨1667407852611497095466113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8892841880594651175819269 1667407852611497095466113)
                ·
                  refine ⟨1250555889458622821599585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667407852611497095466113 1250555889458622821599585)
                  ·
                    refine ⟨937916917093967116199689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250555889458622821599585 937916917093967116199689)
                    ·
                      refine ⟨703437687820475337149767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937916917093967116199689 703437687820475337149767)
                      ·
                        rfl

theorem cell23_1369940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_1369940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369940 prefixEnd_1369940 := by exact prefixLift 1369940
  have htrace : WordTrace (prefixWord ++ tailWord_1369940) baseStart_1369940 baseEnd_1369940 := by
    simpa [prefixWord, tailWord_1369940, baseEnd_1369940] using wordTrace_append hprefix tailTrace_1369940
  have hstable : (prefixWord ++ tailWord_1369940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369940).length < 2 ^ (prefixWord ++ tailWord_1369940).sum := by decide
  have hdescent : baseEnd_1369940 < baseStart_1369940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369946 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_1369946 : Nat := 118140960795 + 1369946 * 2 ^ 59
def prefixEnd_1369946 : Nat := 4983230072969 + 3 ^ 40 * 1369946 * 2
def baseEnd_1369946 : Nat := 78160085411600257074971

theorem tailTrace_1369946 : CollatzResearch.WordTrace tailWord_1369946 prefixEnd_1369946 78160085411600257074971 := by
  unfold tailWord_1369946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12491508873731771248688423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33310690329951389996502461 12491508873731771248688423)
  ·
    refine ⟨18737263310597656873032635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12491508873731771248688423 18737263310597656873032635)
    ·
      refine ⟨28105894965896485309548953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18737263310597656873032635 28105894965896485309548953)
      ·
        refine ⟨21079421224422363982161715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28105894965896485309548953 21079421224422363982161715)
        ·
          refine ⟨31619131836633545973242573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21079421224422363982161715 31619131836633545973242573)
          ·
            refine ⟨11857174438737579739965965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31619131836633545973242573 11857174438737579739965965)
            ·
              refine ⟨4446440414526592402487237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11857174438737579739965965 4446440414526592402487237)
              ·
                refine ⟨833707577723736075466357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4446440414526592402487237 833707577723736075466357)
                ·
                  refine ⟨78160085411600257074971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 833707577723736075466357 78160085411600257074971)
                  ·
                    rfl

theorem cell23_1369946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_1369946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369946 prefixEnd_1369946 := by exact prefixLift 1369946
  have htrace : WordTrace (prefixWord ++ tailWord_1369946) baseStart_1369946 baseEnd_1369946 := by
    simpa [prefixWord, tailWord_1369946, baseEnd_1369946] using wordTrace_append hprefix tailTrace_1369946
  have hstable : (prefixWord ++ tailWord_1369946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369946).length < 2 ^ (prefixWord ++ tailWord_1369946).sum := by decide
  have hdescent : baseEnd_1369946 < baseStart_1369946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1369959 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1369959 : Nat := 118140960795 + 1369959 * 2 ^ 59
def prefixEnd_1369959 : Nat := 4983230072969 + 3 ^ 40 * 1369959 * 2
def baseEnd_1369959 : Nat := 234482481317636920937393

theorem tailTrace_1369959 : CollatzResearch.WordTrace tailWord_1369959 prefixEnd_1369959 234482481317636920937393 := by
  unfold tailWord_1369959
  simp only [CollatzResearch.WordTrace]
  refine ⟨49966509643879988214976931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33311006429253325476651287 49966509643879988214976931)
  ·
    refine ⟨74949764465819982322465397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49966509643879988214976931 74949764465819982322465397)
    ·
      refine ⟨7026540418670623342731131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74949764465819982322465397 7026540418670623342731131)
      ·
        refine ⟨10539810628005935014096697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7026540418670623342731131 10539810628005935014096697)
        ·
          refine ⟨7904857971004451260572523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10539810628005935014096697 7904857971004451260572523)
          ·
            refine ⟨11857286956506676890858785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904857971004451260572523 11857286956506676890858785)
            ·
              refine ⟨8892965217380007668144089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11857286956506676890858785 8892965217380007668144089)
              ·
                refine ⟨6669723913035005751108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8892965217380007668144089 6669723913035005751108067)
                ·
                  refine ⟨10004585869552508626662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6669723913035005751108067 10004585869552508626662101)
                  ·
                    refine ⟨234482481317636920937393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10004585869552508626662101 234482481317636920937393)
                    ·
                      rfl

theorem cell23_1369959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1369959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1369959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1369959 prefixEnd_1369959 := by exact prefixLift 1369959
  have htrace : WordTrace (prefixWord ++ tailWord_1369959) baseStart_1369959 baseEnd_1369959 := by
    simpa [prefixWord, tailWord_1369959, baseEnd_1369959] using wordTrace_append hprefix tailTrace_1369959
  have hstable : (prefixWord ++ tailWord_1369959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1369959).length < 2 ^ (prefixWord ++ tailWord_1369959).sum := by decide
  have hdescent : baseEnd_1369959 < baseStart_1369959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1369959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370013 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_1370013 : Nat := 118140960795 + 1370013 * 2 ^ 59
def prefixEnd_1370013 : Nat := 4983230072969 + 3 ^ 40 * 1370013 * 2
def baseEnd_1370013 : Nat := 703475171908253551536931

theorem tailTrace_1370013 : CollatzResearch.WordTrace tailWord_1370013 prefixEnd_1370013 703475171908253551536931 := by
  unfold tailWord_1370013
  simp only [CollatzResearch.WordTrace]
  refine ⟨49968479185684355437442693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33312319457122903624961795 49968479185684355437442693)
  ·
    refine ⟨9369089847315816644520505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49968479185684355437442693 9369089847315816644520505)
    ·
      refine ⟨7026817385486862483390379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9369089847315816644520505 7026817385486862483390379)
      ·
        refine ⟨10540226078230293725085569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7026817385486862483390379 10540226078230293725085569)
        ·
          refine ⟨7905169558672720293814177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10540226078230293725085569 7905169558672720293814177)
          ·
            refine ⟨5928877169004540220360633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905169558672720293814177 5928877169004540220360633)
            ·
              refine ⟨4446657876753405165270475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928877169004540220360633 4446657876753405165270475)
              ·
                refine ⟨6669986815130107747905713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446657876753405165270475 6669986815130107747905713)
                ·
                  refine ⟨5002490111347580810929285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6669986815130107747905713 5002490111347580810929285)
                  ·
                    refine ⟨937966895877671402049241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002490111347580810929285 937966895877671402049241)
                    ·
                      refine ⟨703475171908253551536931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 937966895877671402049241 703475171908253551536931)
                      ·
                        rfl

theorem cell23_1370013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_1370013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370013 prefixEnd_1370013 := by exact prefixLift 1370013
  have htrace : WordTrace (prefixWord ++ tailWord_1370013) baseStart_1370013 baseEnd_1370013 := by
    simpa [prefixWord, tailWord_1370013, baseEnd_1370013] using wordTrace_append hprefix tailTrace_1370013
  have hstable : (prefixWord ++ tailWord_1370013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370013).length < 2 ^ (prefixWord ++ tailWord_1370013).sum := by decide
  have hdescent : baseEnd_1370013 < baseStart_1370013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370023 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1370023 : Nat := 118140960795 + 1370023 * 2 ^ 59
def prefixEnd_1370023 : Nat := 4983230072969 + 3 ^ 40 * 1370023 * 2
def baseEnd_1370023 : Nat := 234493435571599504137295

theorem tailTrace_1370023 : CollatzResearch.WordTrace tailWord_1370023 prefixEnd_1370023 234493435571599504137295 := by
  unfold tailWord_1370023
  simp only [CollatzResearch.WordTrace]
  refine ⟨49968843915648127145306723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33312562610432084763537815 49968843915648127145306723)
  ·
    refine ⟨74953265873472190717960085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49968843915648127145306723 74953265873472190717960085)
    ·
      refine ⟨3513434337819008939904379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74953265873472190717960085 3513434337819008939904379)
      ·
        refine ⟨5270151506728513409856569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513434337819008939904379 5270151506728513409856569)
        ·
          refine ⟨3952613630046385057392427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5270151506728513409856569 3952613630046385057392427)
          ·
            refine ⟨5928920445069577586088641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952613630046385057392427 5928920445069577586088641)
            ·
              refine ⟨4446690333802183189566481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928920445069577586088641 4446690333802183189566481)
              ·
                refine ⟨3335017750351637392174861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446690333802183189566481 3335017750351637392174861)
                ·
                  refine ⟨1250631656381864022065573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3335017750351637392174861 1250631656381864022065573)
                  ·
                    refine ⟨234493435571599504137295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1250631656381864022065573 234493435571599504137295)
                    ·
                      rfl

theorem cell23_1370023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1370023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370023 prefixEnd_1370023 := by exact prefixLift 1370023
  have htrace : WordTrace (prefixWord ++ tailWord_1370023) baseStart_1370023 baseEnd_1370023 := by
    simpa [prefixWord, tailWord_1370023, baseEnd_1370023] using wordTrace_append hprefix tailTrace_1370023
  have hstable : (prefixWord ++ tailWord_1370023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370023).length < 2 ^ (prefixWord ++ tailWord_1370023).sum := by decide
  have hdescent : baseEnd_1370023 < baseStart_1370023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370070 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1370070 : Nat := 118140960795 + 1370070 * 2 ^ 59
def prefixEnd_1370070 : Nat := 4983230072969 + 3 ^ 40 * 1370070 * 2
def baseEnd_1370070 : Nat := 78167160033951092058241

theorem tailTrace_1370070 : CollatzResearch.WordTrace tailWord_1370070 prefixEnd_1370070 78167160033951092058241 := by
  unfold tailWord_1370070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3123159884154865885766729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33313705430985236114845109 3123159884154865885766729)
  ·
    refine ⟨2342369913116149414325047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3123159884154865885766729 2342369913116149414325047)
    ·
      refine ⟨3513554869674224121487571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342369913116149414325047 3513554869674224121487571)
      ·
        refine ⟨5270332304511336182231357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513554869674224121487571 5270332304511336182231357)
        ·
          refine ⟨1976374614191751068336759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5270332304511336182231357 1976374614191751068336759)
          ·
            refine ⟨2964561921287626602505139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976374614191751068336759 2964561921287626602505139)
            ·
              refine ⟨4446842881931439903757709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964561921287626602505139 4446842881931439903757709)
              ·
                refine ⟨1667566080724289963909141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4446842881931439903757709 1667566080724289963909141)
                ·
                  refine ⟨78167160033951092058241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1667566080724289963909141 78167160033951092058241)
                  ·
                    rfl

theorem cell23_1370070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1370070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370070 prefixEnd_1370070 := by exact prefixLift 1370070
  have htrace : WordTrace (prefixWord ++ tailWord_1370070) baseStart_1370070 baseEnd_1370070 := by
    simpa [prefixWord, tailWord_1370070, baseEnd_1370070] using wordTrace_append hprefix tailTrace_1370070
  have hstable : (prefixWord ++ tailWord_1370070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370070).length < 2 ^ (prefixWord ++ tailWord_1370070).sum := by decide
  have hdescent : baseEnd_1370070 < baseStart_1370070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370083 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 1, 5]
def baseStart_1370083 : Nat := 118140960795 + 1370083 * 2 ^ 59
def prefixEnd_1370083 : Nat := 4983230072969 + 3 ^ 40 * 1370083 * 2
def baseEnd_1370083 : Nat := 234503705184689425887203

theorem tailTrace_1370083 : CollatzResearch.WordTrace tailWord_1370083 prefixEnd_1370083 234503705184689425887203 := by
  unfold tailWord_1370083
  simp only [CollatzResearch.WordTrace]
  refine ⟨49971032295430757392490903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33314021530287171594993935 49971032295430757392490903)
  ·
    refine ⟨74956548443146136088736355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49971032295430757392490903 74956548443146136088736355)
    ·
      refine ⟨112434822664719204133104533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74956548443146136088736355 112434822664719204133104533)
      ·
        refine ⟨5270382312408712693739275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112434822664719204133104533 5270382312408712693739275)
        ·
          refine ⟨7905573468613069040608913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270382312408712693739275 7905573468613069040608913)
          ·
            refine ⟨5929180101459801780456685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905573468613069040608913 5929180101459801780456685)
            ·
              refine ⟨2223442538047425667671257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5929180101459801780456685 2223442538047425667671257)
              ·
                refine ⟨1667581903535569250753443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223442538047425667671257 1667581903535569250753443)
                ·
                  refine ⟨2501372855303353876130165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667581903535569250753443 2501372855303353876130165)
                  ·
                    refine ⟨234503705184689425887203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2501372855303353876130165 234503705184689425887203)
                    ·
                      rfl

theorem cell23_1370083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 5].length) (baseStart_1370083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370083 prefixEnd_1370083 := by exact prefixLift 1370083
  have htrace : WordTrace (prefixWord ++ tailWord_1370083) baseStart_1370083 baseEnd_1370083 := by
    simpa [prefixWord, tailWord_1370083, baseEnd_1370083] using wordTrace_append hprefix tailTrace_1370083
  have hstable : (prefixWord ++ tailWord_1370083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370083).length < 2 ^ (prefixWord ++ tailWord_1370083).sum := by decide
  have hdescent : baseEnd_1370083 < baseStart_1370083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370089 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_1370089 : Nat := 118140960795 + 1370089 * 2 ^ 59
def prefixEnd_1370089 : Nat := 4983230072969 + 3 ^ 40 * 1370089 * 2
def baseEnd_1370089 : Nat := 703514196437995254186581

theorem tailTrace_1370089 : CollatzResearch.WordTrace tailWord_1370089 prefixEnd_1370089 703514196437995254186581 := by
  unfold tailWord_1370089
  simp only [CollatzResearch.WordTrace]
  refine ⟨49971251133409020417209321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33314167422272680278139547 49971251133409020417209321)
  ·
    refine ⟨37478438350056765312906991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49971251133409020417209321 37478438350056765312906991)
    ·
      refine ⟨56217657525085147969360487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37478438350056765312906991 56217657525085147969360487)
      ·
        refine ⟨84326486287627721954040731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56217657525085147969360487 84326486287627721954040731)
        ·
          refine ⟨126489729431441582931061097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84326486287627721954040731 126489729431441582931061097)
          ·
            refine ⟨94867297073581187198295823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126489729431441582931061097 94867297073581187198295823)
            ·
              refine ⟨142300945610371780797443735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94867297073581187198295823 142300945610371780797443735)
              ·
                refine ⟨213451418415557671196165603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142300945610371780797443735 213451418415557671196165603)
                ·
                  refine ⟨320177127623336506794248405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213451418415557671196165603 320177127623336506794248405)
                  ·
                    refine ⟨7504151428671949377990197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 320177127623336506794248405 7504151428671949377990197)
                    ·
                      refine ⟨703514196437995254186581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7504151428671949377990197 703514196437995254186581)
                      ·
                        rfl

theorem cell23_1370089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_1370089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370089 prefixEnd_1370089 := by exact prefixLift 1370089
  have htrace : WordTrace (prefixWord ++ tailWord_1370089) baseStart_1370089 baseEnd_1370089 := by
    simpa [prefixWord, tailWord_1370089, baseEnd_1370089] using wordTrace_append hprefix tailTrace_1370089
  have hstable : (prefixWord ++ tailWord_1370089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370089).length < 2 ^ (prefixWord ++ tailWord_1370089).sum := by decide
  have hdescent : baseEnd_1370089 < baseStart_1370089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370090 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_1370090 : Nat := 118140960795 + 1370090 * 2 ^ 59
def prefixEnd_1370090 : Nat := 4983230072969 + 3 ^ 40 * 1370090 * 2
def baseEnd_1370090 : Nat := 703514709918649750274077

theorem tailTrace_1370090 : CollatzResearch.WordTrace tailWord_1370090 prefixEnd_1370090 703514709918649750274077 := by
  unfold tailWord_1370090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12492821901601349396998931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33314191737603598391997149 12492821901601349396998931)
  ·
    refine ⟨18739232852402024095498397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12492821901601349396998931 18739232852402024095498397)
    ·
      refine ⟨7027212319650759035811899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18739232852402024095498397 7027212319650759035811899)
      ·
        refine ⟨10540818479476138553717849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7027212319650759035811899 10540818479476138553717849)
        ·
          refine ⟨7905613859607103915288387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10540818479476138553717849 7905613859607103915288387)
          ·
            refine ⟨11858420789410655872932581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7905613859607103915288387 11858420789410655872932581)
            ·
              refine ⟨2223453898014497976174859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11858420789410655872932581 2223453898014497976174859)
              ·
                refine ⟨3335180847021746964262289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223453898014497976174859 3335180847021746964262289)
                ·
                  refine ⟨2501385635266310223196717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335180847021746964262289 2501385635266310223196717)
                  ·
                    refine ⟨938019613224866333698769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501385635266310223196717 938019613224866333698769)
                    ·
                      refine ⟨703514709918649750274077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938019613224866333698769 703514709918649750274077)
                      ·
                        rfl

theorem cell23_1370090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_1370090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370090 prefixEnd_1370090 := by exact prefixLift 1370090
  have htrace : WordTrace (prefixWord ++ tailWord_1370090) baseStart_1370090 baseEnd_1370090 := by
    simpa [prefixWord, tailWord_1370090, baseEnd_1370090] using wordTrace_append hprefix tailTrace_1370090
  have hstable : (prefixWord ++ tailWord_1370090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370090).length < 2 ^ (prefixWord ++ tailWord_1370090).sum := by decide
  have hdescent : baseEnd_1370090 < baseStart_1370090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370096 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_1370096 : Nat := 118140960795 + 1370096 * 2 ^ 59
def prefixEnd_1370096 : Nat := 4983230072969 + 3 ^ 40 * 1370096 * 2
def baseEnd_1370096 : Nat := 234505930267525575599683

theorem tailTrace_1370096 : CollatzResearch.WordTrace tailWord_1370096 prefixEnd_1370096 234505930267525575599683 := by
  unfold tailWord_1370096
  simp only [CollatzResearch.WordTrace]
  refine ⟨24985753222191830306357071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33314337629589107075142761 24985753222191830306357071)
  ·
    refine ⟨37478629833287745459535607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24985753222191830306357071 37478629833287745459535607)
    ·
      refine ⟨56217944749931618189303411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37478629833287745459535607 56217944749931618189303411)
      ·
        refine ⟨84326917124897427283955117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56217944749931618189303411 84326917124897427283955117)
        ·
          refine ⟨31622593921836535231483169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84326917124897427283955117 31622593921836535231483169)
          ·
            refine ⟨23716945441377401423612377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31622593921836535231483169 23716945441377401423612377)
            ·
              refine ⟨17787709081033051067709283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23716945441377401423612377 17787709081033051067709283)
              ·
                refine ⟨26681563621549576601563925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17787709081033051067709283 26681563621549576601563925)
                ·
                  refine ⟨1250698294760136403198309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26681563621549576601563925 1250698294760136403198309)
                  ·
                    refine ⟨234505930267525575599683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1250698294760136403198309 234505930267525575599683)
                    ·
                      rfl

theorem cell23_1370096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_1370096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370096 prefixEnd_1370096 := by exact prefixLift 1370096
  have htrace : WordTrace (prefixWord ++ tailWord_1370096) baseStart_1370096 baseEnd_1370096 := by
    simpa [prefixWord, tailWord_1370096, baseEnd_1370096] using wordTrace_append hprefix tailTrace_1370096
  have hstable : (prefixWord ++ tailWord_1370096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370096).length < 2 ^ (prefixWord ++ tailWord_1370096).sum := by decide
  have hdescent : baseEnd_1370096 < baseStart_1370096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370120 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_1370120 : Nat := 118140960795 + 1370120 * 2 ^ 59
def prefixEnd_1370120 : Nat := 4983230072969 + 3 ^ 40 * 1370120 * 2
def baseEnd_1370120 : Nat := 703530114338284632898939

theorem tailTrace_1370120 : CollatzResearch.WordTrace tailWord_1370120 prefixEnd_1370120 703530114338284632898939 := by
  unfold tailWord_1370120
  simp only [CollatzResearch.WordTrace]
  refine ⟨24986190898148356355793907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33314921197531141807725209 24986190898148356355793907)
  ·
    refine ⟨37479286347222534533690861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24986190898148356355793907 37479286347222534533690861)
    ·
      refine ⟨14054732380208450450134073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37479286347222534533690861 14054732380208450450134073)
      ·
        refine ⟨10541049285156337837600555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14054732380208450450134073 10541049285156337837600555)
        ·
          refine ⟨15811573927734506756400833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10541049285156337837600555 15811573927734506756400833)
          ·
            refine ⟨11858680445800880067300625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15811573927734506756400833 11858680445800880067300625)
            ·
              refine ⟨8894010334350660050475469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11858680445800880067300625 8894010334350660050475469)
              ·
                refine ⟨3335253875381497518928301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8894010334350660050475469 3335253875381497518928301)
                ·
                  refine ⟨1250720203268061569598113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3335253875381497518928301 1250720203268061569598113)
                  ·
                    refine ⟨938040152451046177198585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250720203268061569598113 938040152451046177198585)
                    ·
                      refine ⟨703530114338284632898939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938040152451046177198585 703530114338284632898939)
                      ·
                        rfl

theorem cell23_1370120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_1370120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370120 prefixEnd_1370120 := by exact prefixLift 1370120
  have htrace : WordTrace (prefixWord ++ tailWord_1370120) baseStart_1370120 baseEnd_1370120 := by
    simpa [prefixWord, tailWord_1370120, baseEnd_1370120] using wordTrace_append hprefix tailTrace_1370120
  have hstable : (prefixWord ++ tailWord_1370120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370120).length < 2 ^ (prefixWord ++ tailWord_1370120).sum := by decide
  have hdescent : baseEnd_1370120 < baseStart_1370120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370154 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_1370154 : Nat := 118140960795 + 1370154 * 2 ^ 59
def prefixEnd_1370154 : Nat := 4983230072969 + 3 ^ 40 * 1370154 * 2
def baseEnd_1370154 : Nat := 703547572680537499873783

theorem tailTrace_1370154 : CollatzResearch.WordTrace tailWord_1370154 prefixEnd_1370154 703547572680537499873783 := by
  unfold tailWord_1370154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12493405469543384129581379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33315747918782357678883677 12493405469543384129581379)
  ·
    refine ⟨18740108204315076194372069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12493405469543384129581379 18740108204315076194372069)
    ·
      refine ⟨3513770288309076786444763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18740108204315076194372069 3513770288309076786444763)
      ·
        refine ⟨5270655432463615179667145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513770288309076786444763 5270655432463615179667145)
        ·
          refine ⟨3952991574347711384750359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5270655432463615179667145 3952991574347711384750359)
          ·
            refine ⟨5929487361521567077125539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952991574347711384750359 5929487361521567077125539)
            ·
              refine ⟨8894231042282350615688309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929487361521567077125539 8894231042282350615688309)
              ·
                refine ⟨833834160213970370220779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8894231042282350615688309 833834160213970370220779)
                ·
                  refine ⟨1250751240320955555331169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833834160213970370220779 1250751240320955555331169)
                  ·
                    refine ⟨938063430240716666498377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250751240320955555331169 938063430240716666498377)
                    ·
                      refine ⟨703547572680537499873783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938063430240716666498377 703547572680537499873783)
                      ·
                        rfl

theorem cell23_1370154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_1370154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370154 prefixEnd_1370154 := by exact prefixLift 1370154
  have htrace : WordTrace (prefixWord ++ tailWord_1370154) baseStart_1370154 baseEnd_1370154 := by
    simpa [prefixWord, tailWord_1370154, baseEnd_1370154] using wordTrace_append hprefix tailTrace_1370154
  have hstable : (prefixWord ++ tailWord_1370154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370154).length < 2 ^ (prefixWord ++ tailWord_1370154).sum := by decide
  have hdescent : baseEnd_1370154 < baseStart_1370154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370164 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1370164 : Nat := 118140960795 + 1370164 * 2 ^ 59
def prefixEnd_1370164 : Nat := 4983230072969 + 3 ^ 40 * 1370164 * 2
def baseEnd_1370164 : Nat := 234517569162360820249579

theorem tailTrace_1370164 : CollatzResearch.WordTrace tailWord_1370164 prefixEnd_1370164 234517569162360820249579 := by
  unfold tailWord_1370164
  simp only [CollatzResearch.WordTrace]
  refine ⟨24986993304068654113094773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33315991072091538817459697 24986993304068654113094773)
  ·
    refine ⟨2342530622256436323102635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24986993304068654113094773 2342530622256436323102635)
    ·
      refine ⟨3513795933384654484653953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342530622256436323102635 3513795933384654484653953)
      ·
        refine ⟨2635346950038490863490465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3513795933384654484653953 2635346950038490863490465)
        ·
          refine ⟨1976510212528868147617849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2635346950038490863490465 1976510212528868147617849)
          ·
            refine ⟨1482382659396651110713387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1976510212528868147617849 1482382659396651110713387)
            ·
              refine ⟨2223573989094976666070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1482382659396651110713387 2223573989094976666070081)
              ·
                refine ⟨1667680491821232499552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223573989094976666070081 1667680491821232499552561)
                ·
                  refine ⟨1250760368865924374664421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667680491821232499552561 1250760368865924374664421)
                  ·
                    refine ⟨234517569162360820249579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1250760368865924374664421 234517569162360820249579)
                    ·
                      rfl

theorem cell23_1370164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1370164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370164 prefixEnd_1370164 := by exact prefixLift 1370164
  have htrace : WordTrace (prefixWord ++ tailWord_1370164) baseStart_1370164 baseEnd_1370164 := by
    simpa [prefixWord, tailWord_1370164, baseEnd_1370164] using wordTrace_append hprefix tailTrace_1370164
  have hstable : (prefixWord ++ tailWord_1370164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370164).length < 2 ^ (prefixWord ++ tailWord_1370164).sum := by decide
  have hdescent : baseEnd_1370164 < baseStart_1370164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370197 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1370197 : Nat := 118140960795 + 1370197 * 2 ^ 59
def prefixEnd_1370197 : Nat := 4983230072969 + 3 ^ 40 * 1370197 * 2
def baseEnd_1370197 : Nat := 703569652348680831636085

theorem tailTrace_1370197 : CollatzResearch.WordTrace tailWord_1370197 prefixEnd_1370197 703569652348680831636085 := by
  unfold tailWord_1370197
  simp only [CollatzResearch.WordTrace]
  refine ⟨49975190217017754862140845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33316793478011836574760563 49975190217017754862140845)
  ·
    refine ⟨18740696331381658073302817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49975190217017754862140845 18740696331381658073302817)
    ·
      refine ⟨14055522248536243554977113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18740696331381658073302817 14055522248536243554977113)
      ·
        refine ⟨10541641686402182666232835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14055522248536243554977113 10541641686402182666232835)
        ·
          refine ⟨15812462529603273999349253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10541641686402182666232835 15812462529603273999349253)
          ·
            refine ⟨2964836724300613874877985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15812462529603273999349253 2964836724300613874877985)
            ·
              refine ⟨2223627543225460406158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2964836724300613874877985 2223627543225460406158489)
              ·
                refine ⟨1667720657419095304618867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2223627543225460406158489 1667720657419095304618867)
                ·
                  refine ⟨2501580986128642956928301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667720657419095304618867 2501580986128642956928301)
                  ·
                    refine ⟨938092869798241108848113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501580986128642956928301 938092869798241108848113)
                    ·
                      refine ⟨703569652348680831636085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938092869798241108848113 703569652348680831636085)
                      ·
                        rfl

theorem cell23_1370197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1370197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370197 prefixEnd_1370197 := by exact prefixLift 1370197
  have htrace : WordTrace (prefixWord ++ tailWord_1370197) baseStart_1370197 baseEnd_1370197 := by
    simpa [prefixWord, tailWord_1370197, baseEnd_1370197] using wordTrace_append hprefix tailTrace_1370197
  have hstable : (prefixWord ++ tailWord_1370197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370197).length < 2 ^ (prefixWord ++ tailWord_1370197).sum := by decide
  have hdescent : baseEnd_1370197 < baseStart_1370197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370213 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1370213 : Nat := 118140960795 + 1370213 * 2 ^ 59
def prefixEnd_1370213 : Nat := 4983230072969 + 3 ^ 40 * 1370213 * 2
def baseEnd_1370213 : Nat := 703577868039152769036011

theorem tailTrace_1370213 : CollatzResearch.WordTrace tailWord_1370213 prefixEnd_1370213 703577868039152769036011 := by
  unfold tailWord_1370213
  simp only [CollatzResearch.WordTrace]
  refine ⟨49975773784959789594723293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33317182523306526396482195 49975773784959789594723293)
  ·
    refine ⟨18740915169359921098021235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49975773784959789594723293 18740915169359921098021235)
    ·
      refine ⟨28111372754039881647031853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18740915169359921098021235 28111372754039881647031853)
      ·
        refine ⟨10541764782764955617636945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28111372754039881647031853 10541764782764955617636945)
        ·
          refine ⟨7906323587073716713227709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10541764782764955617636945 7906323587073716713227709)
          ·
            refine ⟨2964871345152643767460391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7906323587073716713227709 2964871345152643767460391)
            ·
              refine ⟨4447307017728965651190587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964871345152643767460391 4447307017728965651190587)
              ·
                refine ⟨6670960526593448476785881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4447307017728965651190587 6670960526593448476785881)
                ·
                  refine ⟨5003220394945086357589411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6670960526593448476785881 5003220394945086357589411)
                  ·
                    refine ⟨7504830592417629536384117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5003220394945086357589411 7504830592417629536384117)
                    ·
                      refine ⟨703577868039152769036011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7504830592417629536384117 703577868039152769036011)
                      ·
                        rfl

theorem cell23_1370213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1370213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370213 prefixEnd_1370213 := by exact prefixLift 1370213
  have htrace : WordTrace (prefixWord ++ tailWord_1370213) baseStart_1370213 baseEnd_1370213 := by
    simpa [prefixWord, tailWord_1370213, baseEnd_1370213] using wordTrace_append hprefix tailTrace_1370213
  have hstable : (prefixWord ++ tailWord_1370213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370213).length < 2 ^ (prefixWord ++ tailWord_1370213).sum := by decide
  have hdescent : baseEnd_1370213 < baseStart_1370213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370233 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 7]
def baseStart_1370233 : Nat := 118140960795 + 1370233 * 2 ^ 59
def prefixEnd_1370233 : Nat := 4983230072969 + 3 ^ 40 * 1370233 * 2
def baseEnd_1370233 : Nat := 78176459739138076753991

theorem tailTrace_1370233 : CollatzResearch.WordTrace tailWord_1370233 prefixEnd_1370233 78176459739138076753991 := by
  unfold tailWord_1370233
  simp only [CollatzResearch.WordTrace]
  refine ⟨49976503244887333010451353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33317668829924888673634235 49976503244887333010451353)
  ·
    refine ⟨37482377433665499757838515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49976503244887333010451353 37482377433665499757838515)
    ·
      refine ⟨56223566150498249636757773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37482377433665499757838515 56223566150498249636757773)
      ·
        refine ⟨21083837306436843613784165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56223566150498249636757773 21083837306436843613784165)
        ·
          refine ⟨3953219494956908177584531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21083837306436843613784165 3953219494956908177584531)
          ·
            refine ⟨5929829242435362266376797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953219494956908177584531 5929829242435362266376797)
            ·
              refine ⟨2223685965913260849891299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5929829242435362266376797 2223685965913260849891299)
              ·
                refine ⟨3335528948869891274836949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2223685965913260849891299 3335528948869891274836949)
                ·
                  refine ⟨78176459739138076753991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3335528948869891274836949 78176459739138076753991)
                  ·
                    rfl

theorem cell23_1370233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_1370233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370233 prefixEnd_1370233 := by exact prefixLift 1370233
  have htrace : WordTrace (prefixWord ++ tailWord_1370233) baseStart_1370233 baseEnd_1370233 := by
    simpa [prefixWord, tailWord_1370233, baseEnd_1370233] using wordTrace_append hprefix tailTrace_1370233
  have hstable : (prefixWord ++ tailWord_1370233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370233).length < 2 ^ (prefixWord ++ tailWord_1370233).sum := by decide
  have hdescent : baseEnd_1370233 < baseStart_1370233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370256 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1370256 : Nat := 118140960795 + 1370256 * 2 ^ 59
def prefixEnd_1370256 : Nat := 4983230072969 + 3 ^ 40 * 1370256 * 2
def baseEnd_1370256 : Nat := 703599947707296100798313

theorem tailTrace_1370256 : CollatzResearch.WordTrace tailWord_1370256 prefixEnd_1370256 703599947707296100798313 := by
  unfold tailWord_1370256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24988671061902003969269311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33318228082536005292359081 24988671061902003969269311)
  ·
    refine ⟨37483006592853005953903967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24988671061902003969269311 37483006592853005953903967)
    ·
      refine ⟨56224509889279508930855951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37483006592853005953903967 56224509889279508930855951)
      ·
        refine ⟨84336764833919263396283927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56224509889279508930855951 84336764833919263396283927)
        ·
          refine ⟨126505147250878895094425891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84336764833919263396283927 126505147250878895094425891)
          ·
            refine ⟨189757720876318342641638837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126505147250878895094425891 189757720876318342641638837)
            ·
              refine ⟨17789786332154844622653641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189757720876318342641638837 17789786332154844622653641)
              ·
                refine ⟨13342339749116133466990231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17789786332154844622653641 13342339749116133466990231)
                ·
                  refine ⟨20013509623674200200485347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13342339749116133466990231 20013509623674200200485347)
                  ·
                    refine ⟨30020264435511300300728021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20013509623674200200485347 30020264435511300300728021)
                    ·
                      refine ⟨703599947707296100798313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30020264435511300300728021 703599947707296100798313)
                      ·
                        rfl

theorem cell23_1370256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1370256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370256 prefixEnd_1370256 := by exact prefixLift 1370256
  have htrace : WordTrace (prefixWord ++ tailWord_1370256) baseStart_1370256 baseEnd_1370256 := by
    simpa [prefixWord, tailWord_1370256, baseEnd_1370256] using wordTrace_append hprefix tailTrace_1370256
  have hstable : (prefixWord ++ tailWord_1370256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370256).length < 2 ^ (prefixWord ++ tailWord_1370256).sum := by decide
  have hdescent : baseEnd_1370256 < baseStart_1370256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370273 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1370273 : Nat := 118140960795 + 1370273 * 2 ^ 59
def prefixEnd_1370273 : Nat := 4983230072969 + 3 ^ 40 * 1370273 * 2
def baseEnd_1370273 : Nat := 703608676878422534285735

theorem tailTrace_1370273 : CollatzResearch.WordTrace tailWord_1370273 prefixEnd_1370273 703608676878422534285735 := by
  unfold tailWord_1370273
  simp only [CollatzResearch.WordTrace]
  refine ⟨49977962164742419841907473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33318641443161613227938315 49977962164742419841907473)
  ·
    refine ⟨37483471623556814881430605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49977962164742419841907473 37483471623556814881430605)
    ·
      refine ⟨14056301858833805580536477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37483471623556814881430605 14056301858833805580536477)
      ·
        refine ⟨5271113197062677092701179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14056301858833805580536477 5271113197062677092701179)
        ·
          refine ⟨7906669795594015639051769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271113197062677092701179 7906669795594015639051769)
          ·
            refine ⟨5930002346695511729288827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7906669795594015639051769 5930002346695511729288827)
            ·
              refine ⟨8895003520043267593933241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5930002346695511729288827 8895003520043267593933241)
              ·
                refine ⟨6671252640032450695449931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8895003520043267593933241 6671252640032450695449931)
                ·
                  refine ⟨10006878960048676043174897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671252640032450695449931 10006878960048676043174897)
                  ·
                    refine ⟨7505159220036507032381173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10006878960048676043174897 7505159220036507032381173)
                    ·
                      refine ⟨703608676878422534285735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7505159220036507032381173 703608676878422534285735)
                      ·
                        rfl

theorem cell23_1370273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1370273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370273 prefixEnd_1370273 := by exact prefixLift 1370273
  have htrace : WordTrace (prefixWord ++ tailWord_1370273) baseStart_1370273 baseEnd_1370273 := by
    simpa [prefixWord, tailWord_1370273, baseEnd_1370273] using wordTrace_append hprefix tailTrace_1370273
  have hstable : (prefixWord ++ tailWord_1370273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370273).length < 2 ^ (prefixWord ++ tailWord_1370273).sum := by decide
  have hdescent : baseEnd_1370273 < baseStart_1370273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370303 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3]
def baseStart_1370303 : Nat := 118140960795 + 1370303 * 2 ^ 59
def prefixEnd_1370303 : Nat := 4983230072969 + 3 ^ 40 * 1370303 * 2
def baseEnd_1370303 : Nat := 703624081298057416910597

theorem tailTrace_1370303 : CollatzResearch.WordTrace tailWord_1370303 prefixEnd_1370303 703624081298057416910597 := by
  unfold tailWord_1370303
  simp only [CollatzResearch.WordTrace]
  refine ⟨49979056354633734965499563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33319370903089156643666375 49979056354633734965499563)
  ·
    refine ⟨74968584531950602448249345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49979056354633734965499563 74968584531950602448249345)
    ·
      refine ⟨56226438398962951836187009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74968584531950602448249345 56226438398962951836187009)
      ·
        refine ⟨42169828799222213877140257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56226438398962951836187009 42169828799222213877140257)
        ·
          refine ⟨31627371599416660407855193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42169828799222213877140257 31627371599416660407855193)
          ·
            refine ⟨23720528699562495305891395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31627371599416660407855193 23720528699562495305891395)
            ·
              refine ⟨35580793049343742958837093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23720528699562495305891395 35580793049343742958837093)
              ·
                refine ⟨6671398696751951804781955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35580793049343742958837093 6671398696751951804781955)
                ·
                  refine ⟨10007098045127927707172933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6671398696751951804781955 10007098045127927707172933)
                  ·
                    refine ⟨1876330883461486445094925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10007098045127927707172933 1876330883461486445094925)
                    ·
                      refine ⟨703624081298057416910597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1876330883461486445094925 703624081298057416910597)
                      ·
                        rfl

theorem cell23_1370303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_1370303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370303 prefixEnd_1370303 := by exact prefixLift 1370303
  have htrace : WordTrace (prefixWord ++ tailWord_1370303) baseStart_1370303 baseEnd_1370303 := by
    simpa [prefixWord, tailWord_1370303, baseEnd_1370303] using wordTrace_append hprefix tailTrace_1370303
  have hstable : (prefixWord ++ tailWord_1370303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370303).length < 2 ^ (prefixWord ++ tailWord_1370303).sum := by decide
  have hdescent : baseEnd_1370303 < baseStart_1370303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370353 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1370353 : Nat := 118140960795 + 1370353 * 2 ^ 59
def prefixEnd_1370353 : Nat := 4983230072969 + 3 ^ 40 * 1370353 * 2
def baseEnd_1370353 : Nat := 234549918443594073761789

theorem tailTrace_1370353 : CollatzResearch.WordTrace tailWord_1370353 prefixEnd_1370353 234549918443594073761789 := by
  unfold tailWord_1370353
  simp only [CollatzResearch.WordTrace]
  refine ⟨49980880004452593504819713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33320586669635062336546475 49980880004452593504819713)
  ·
    refine ⟨37485660003339445128614785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49980880004452593504819713 37485660003339445128614785)
    ·
      refine ⟨28114245002504583846461089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37485660003339445128614785 28114245002504583846461089)
      ·
        refine ⟨21085683751878437884845817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28114245002504583846461089 21085683751878437884845817)
        ·
          refine ⟨15814262813908828413634363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21085683751878437884845817 15814262813908828413634363)
          ·
            refine ⟨23721394220863242620451545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15814262813908828413634363 23721394220863242620451545)
            ·
              refine ⟨17791045665647431965338659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23721394220863242620451545 17791045665647431965338659)
              ·
                refine ⟨26686568498471147948007989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17791045665647431965338659 26686568498471147948007989)
                ·
                  refine ⟨2501865796731670120125749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26686568498471147948007989 2501865796731670120125749)
                  ·
                    refine ⟨234549918443594073761789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2501865796731670120125749 234549918443594073761789)
                    ·
                      rfl

theorem cell23_1370353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1370353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370353 prefixEnd_1370353 := by exact prefixLift 1370353
  have htrace : WordTrace (prefixWord ++ tailWord_1370353) baseStart_1370353 baseEnd_1370353 := by
    simpa [prefixWord, tailWord_1370353, baseEnd_1370353] using wordTrace_append hprefix tailTrace_1370353
  have hstable : (prefixWord ++ tailWord_1370353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370353).length < 2 ^ (prefixWord ++ tailWord_1370353).sum := by decide
  have hdescent : baseEnd_1370353 < baseStart_1370353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370383 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 1, 6]
def baseStart_1370383 : Nat := 118140960795 + 1370383 * 2 ^ 59
def prefixEnd_1370383 : Nat := 4983230072969 + 3 ^ 40 * 1370383 * 2
def baseEnd_1370383 : Nat := 234555053250139034636743

theorem tailTrace_1370383 : CollatzResearch.WordTrace tailWord_1370383 prefixEnd_1370383 234555053250139034636743 := by
  unfold tailWord_1370383
  simp only [CollatzResearch.WordTrace]
  refine ⟨49981974194343908628411803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33321316129562605752274535 49981974194343908628411803)
  ·
    refine ⟨74972961291515862942617705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49981974194343908628411803 74972961291515862942617705)
    ·
      refine ⟨56229720968636897206963279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74972961291515862942617705 56229720968636897206963279)
      ·
        refine ⟨84344581452955345810444919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56229720968636897206963279 84344581452955345810444919)
        ·
          refine ⟨126516872179433018715667379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84344581452955345810444919 126516872179433018715667379)
          ·
            refine ⟨189775308269149528073501069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126516872179433018715667379 189775308269149528073501069)
            ·
              refine ⟨71165740600931073027562901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189775308269149528073501069 71165740600931073027562901)
              ·
                refine ⟨3335894090668644048167011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71165740600931073027562901 3335894090668644048167011)
                ·
                  refine ⟨5003841136002966072250517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335894090668644048167011 5003841136002966072250517)
                  ·
                    refine ⟨234555053250139034636743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5003841136002966072250517 234555053250139034636743)
                    ·
                      rfl

theorem cell23_1370383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_1370383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370383 prefixEnd_1370383 := by exact prefixLift 1370383
  have htrace : WordTrace (prefixWord ++ tailWord_1370383) baseStart_1370383 baseEnd_1370383 := by
    simpa [prefixWord, tailWord_1370383, baseEnd_1370383] using wordTrace_append hprefix tailTrace_1370383
  have hstable : (prefixWord ++ tailWord_1370383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370383).length < 2 ^ (prefixWord ++ tailWord_1370383).sum := by decide
  have hdescent : baseEnd_1370383 < baseStart_1370383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370394 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_1370394 : Nat := 118140960795 + 1370394 * 2 ^ 59
def prefixEnd_1370394 : Nat := 4983230072969 + 3 ^ 40 * 1370394 * 2
def baseEnd_1370394 : Nat := 703670808037616560872679

theorem tailTrace_1370394 : CollatzResearch.WordTrace tailWord_1370394 prefixEnd_1370394 703670808037616560872679 := by
  unfold tailWord_1370394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12495593849326014376765559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33321583598202705004708157 12495593849326014376765559)
  ·
    refine ⟨18743390773989021565148339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12495593849326014376765559 18743390773989021565148339)
    ·
      refine ⟨28115086160983532347722509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18743390773989021565148339 28115086160983532347722509)
      ·
        refine ⟨10543157310368824630395941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28115086160983532347722509 10543157310368824630395941)
        ·
          refine ⟨1976841995694154618199239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10543157310368824630395941 1976841995694154618199239)
          ·
            refine ⟨2965262993541231927298859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976841995694154618199239 2965262993541231927298859)
            ·
              refine ⟨4447894490311847890948289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965262993541231927298859 4447894490311847890948289)
              ·
                refine ⟨3335920867733885918211217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4447894490311847890948289 3335920867733885918211217)
                ·
                  refine ⟨2501940650800414438658413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3335920867733885918211217 2501940650800414438658413)
                  ·
                    refine ⟨938227744050155414496905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501940650800414438658413 938227744050155414496905)
                    ·
                      refine ⟨703670808037616560872679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938227744050155414496905 703670808037616560872679)
                      ·
                        rfl

theorem cell23_1370394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_1370394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370394 prefixEnd_1370394 := by exact prefixLift 1370394
  have htrace : WordTrace (prefixWord ++ tailWord_1370394) baseStart_1370394 baseEnd_1370394 := by
    simpa [prefixWord, tailWord_1370394, baseEnd_1370394] using wordTrace_append hprefix tailTrace_1370394
  have hstable : (prefixWord ++ tailWord_1370394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370394).length < 2 ^ (prefixWord ++ tailWord_1370394).sum := by decide
  have hdescent : baseEnd_1370394 < baseStart_1370394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370403 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1370403 : Nat := 118140960795 + 1370403 * 2 ^ 59
def prefixEnd_1370403 : Nat := 4983230072969 + 3 ^ 40 * 1370403 * 2
def baseEnd_1370403 : Nat := 703675429363507025660137

theorem tailTrace_1370403 : CollatzResearch.WordTrace tailWord_1370403 prefixEnd_1370403 703675429363507025660137 := by
  unfold tailWord_1370403
  simp only [CollatzResearch.WordTrace]
  refine ⟨49982703654271452044139863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33321802436180968029426575 49982703654271452044139863)
  ·
    refine ⟨74974055481407178066209795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49982703654271452044139863 74974055481407178066209795)
    ·
      refine ⟨112461083222110767099314693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74974055481407178066209795 112461083222110767099314693)
      ·
        refine ⟨21086453104145768831121505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112461083222110767099314693 21086453104145768831121505)
        ·
          refine ⟨15814839828109326623341129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21086453104145768831121505 15814839828109326623341129)
          ·
            refine ⟨11861129871081994967505847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15814839828109326623341129 11861129871081994967505847)
            ·
              refine ⟨17791694806622992451258771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861129871081994967505847 17791694806622992451258771)
              ·
                refine ⟨26687542209934488676888157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17791694806622992451258771 26687542209934488676888157)
                ·
                  refine ⟨10007828328725433253833059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26687542209934488676888157 10007828328725433253833059)
                  ·
                    refine ⟨15011742493088149880749589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10007828328725433253833059 15011742493088149880749589)
                    ·
                      refine ⟨703675429363507025660137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15011742493088149880749589 703675429363507025660137)
                      ·
                        rfl

theorem cell23_1370403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1370403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370403 prefixEnd_1370403 := by exact prefixLift 1370403
  have htrace : WordTrace (prefixWord ++ tailWord_1370403) baseStart_1370403 baseEnd_1370403 := by
    simpa [prefixWord, tailWord_1370403, baseEnd_1370403] using wordTrace_append hprefix tailTrace_1370403
  have hstable : (prefixWord ++ tailWord_1370403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370403).length < 2 ^ (prefixWord ++ tailWord_1370403).sum := by decide
  have hdescent : baseEnd_1370403 < baseStart_1370403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370430 : List Nat := [4, 2, 1, 2, 1, 2, 2, 9]
def baseStart_1370430 : Nat := 118140960795 + 1370430 * 2 ^ 59
def prefixEnd_1370430 : Nat := 4983230072969 + 3 ^ 40 * 1370430 * 2
def baseEnd_1370430 : Nat := 26062566420043645186019

theorem tailTrace_1370430 : CollatzResearch.WordTrace tailWord_1370430 prefixEnd_1370430 26062566420043645186019 := by
  unfold tailWord_1370430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247961053146704456921593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33322458950115757103581829 6247961053146704456921593)
  ·
    refine ⟨4685970789860028342691195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6247961053146704456921593 4685970789860028342691195)
    ·
      refine ⟨7028956184790042514036793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4685970789860028342691195 7028956184790042514036793)
      ·
        refine ⟨5271717138592531885527595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7028956184790042514036793 5271717138592531885527595)
        ·
          refine ⟨7907575707888797828291393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271717138592531885527595 7907575707888797828291393)
          ·
            refine ⟨5930681780916598371218545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7907575707888797828291393 5930681780916598371218545)
            ·
              refine ⟨4448011335687448778413909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5930681780916598371218545 4448011335687448778413909)
              ·
                refine ⟨26062566420043645186019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4448011335687448778413909 26062566420043645186019)
                ·
                  rfl

theorem cell23_1370430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_1370430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370430 prefixEnd_1370430 := by exact prefixLift 1370430
  have htrace : WordTrace (prefixWord ++ tailWord_1370430) baseStart_1370430 baseEnd_1370430 := by
    simpa [prefixWord, tailWord_1370430, baseEnd_1370430] using wordTrace_append hprefix tailTrace_1370430
  have hstable : (prefixWord ++ tailWord_1370430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370430).length < 2 ^ (prefixWord ++ tailWord_1370430).sum := by decide
  have hdescent : baseEnd_1370430 < baseStart_1370430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370440 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_1370440 : Nat := 118140960795 + 1370440 * 2 ^ 59
def prefixEnd_1370440 : Nat := 4983230072969 + 3 ^ 40 * 1370440 * 2
def baseEnd_1370440 : Nat := 703694428147723380897467

theorem tailTrace_1370440 : CollatzResearch.WordTrace tailWord_1370440 prefixEnd_1370440 703694428147723380897467 := by
  unfold tailWord_1370440
  simp only [CollatzResearch.WordTrace]
  refine ⟨24992026577568703681618387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33322702103424938242157849 24992026577568703681618387)
  ·
    refine ⟨37488039866353055522427581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24992026577568703681618387 37488039866353055522427581)
    ·
      refine ⟨14058014949882395820910343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37488039866353055522427581 14058014949882395820910343)
      ·
        refine ⟨21087022424823593731365515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14058014949882395820910343 21087022424823593731365515)
        ·
          refine ⟨31630533637235390597048273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21087022424823593731365515 31630533637235390597048273)
          ·
            refine ⟨23722900227926542947786205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31630533637235390597048273 23722900227926542947786205)
            ·
              refine ⟨8896087585472453605419827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23722900227926542947786205 8896087585472453605419827)
              ·
                refine ⟨13344131378208680408129741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896087585472453605419827 13344131378208680408129741)
                ·
                  refine ⟨5004049266828255153048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13344131378208680408129741 5004049266828255153048653)
                  ·
                    refine ⟨1876518475060595682393245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5004049266828255153048653 1876518475060595682393245)
                    ·
                      refine ⟨703694428147723380897467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1876518475060595682393245 703694428147723380897467)
                      ·
                        rfl

theorem cell23_1370440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_1370440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370440 prefixEnd_1370440 := by exact prefixLift 1370440
  have htrace : WordTrace (prefixWord ++ tailWord_1370440) baseStart_1370440 baseEnd_1370440 := by
    simpa [prefixWord, tailWord_1370440, baseEnd_1370440] using wordTrace_append hprefix tailTrace_1370440
  have hstable : (prefixWord ++ tailWord_1370440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370440).length < 2 ^ (prefixWord ++ tailWord_1370440).sum := by decide
  have hdescent : baseEnd_1370440 < baseStart_1370440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370444 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1370444 : Nat := 118140960795 + 1370444 * 2 ^ 59
def prefixEnd_1370444 : Nat := 4983230072969 + 3 ^ 40 * 1370444 * 2
def baseEnd_1370444 : Nat := 703696482070341365247449

theorem tailTrace_1370444 : CollatzResearch.WordTrace tailWord_1370444 prefixEnd_1370444 703696482070341365247449 := by
  unfold tailWord_1370444
  simp only [CollatzResearch.WordTrace]
  refine ⟨24992099523561458023191193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33322799364748610697588257 24992099523561458023191193)
  ·
    refine ⟨18744074642671093517393395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24992099523561458023191193 18744074642671093517393395)
    ·
      refine ⟨28116111964006640276090093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18744074642671093517393395 28116111964006640276090093)
      ·
        refine ⟨10543541986502490103533785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28116111964006640276090093 10543541986502490103533785)
        ·
          refine ⟨7907656489876867577650339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10543541986502490103533785 7907656489876867577650339)
          ·
            refine ⟨11861484734815301366475509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907656489876867577650339 11861484734815301366475509)
            ·
              refine ⟨1112014193888934503107079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11861484734815301366475509 1112014193888934503107079)
              ·
                refine ⟨1668021290833401754660619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112014193888934503107079 1668021290833401754660619)
                ·
                  refine ⟨2502031936250102631990929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668021290833401754660619 2502031936250102631990929)
                  ·
                    refine ⟨1876523952187576973993197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2502031936250102631990929 1876523952187576973993197)
                    ·
                      refine ⟨703696482070341365247449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1876523952187576973993197 703696482070341365247449)
                      ·
                        rfl

theorem cell23_1370444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1370444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370444 prefixEnd_1370444 := by exact prefixLift 1370444
  have htrace : WordTrace (prefixWord ++ tailWord_1370444) baseStart_1370444 baseEnd_1370444 := by
    simpa [prefixWord, tailWord_1370444, baseEnd_1370444] using wordTrace_append hprefix tailTrace_1370444
  have hstable : (prefixWord ++ tailWord_1370444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370444).length < 2 ^ (prefixWord ++ tailWord_1370444).sum := by decide
  have hdescent : baseEnd_1370444 < baseStart_1370444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370467 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 5, 3, 2]
def baseStart_1370467 : Nat := 118140960795 + 1370467 * 2 ^ 59
def prefixEnd_1370467 : Nat := 4983230072969 + 3 ^ 40 * 1370467 * 2
def baseEnd_1370467 : Nat := 703708292125394775259843

theorem tailTrace_1370467 : CollatzResearch.WordTrace tailWord_1370467 prefixEnd_1370467 703708292125394775259843 := by
  unfold tailWord_1370467
  simp only [CollatzResearch.WordTrace]
  refine ⟨49985037926039590974469655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33323358617359727316313103 49985037926039590974469655)
  ·
    refine ⟨74977556889059386461704483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49985037926039590974469655 74977556889059386461704483)
    ·
      refine ⟨112466335333589079692556725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74977556889059386461704483 112466335333589079692556725)
      ·
        refine ⟨10543718937523976221177193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112466335333589079692556725 10543718937523976221177193)
        ·
          refine ⟨7907789203142982165882895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10543718937523976221177193 7907789203142982165882895)
          ·
            refine ⟨11861683804714473248824343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907789203142982165882895 11861683804714473248824343)
            ·
              refine ⟨17792525707071709873236515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861683804714473248824343 17792525707071709873236515)
              ·
                refine ⟨26688788560607564809854773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17792525707071709873236515 26688788560607564809854773)
                ·
                  refine ⟨2502073927556959200923885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26688788560607564809854773 2502073927556959200923885)
                  ·
                    refine ⟨938277722833859700346457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2502073927556959200923885 938277722833859700346457)
                    ·
                      refine ⟨703708292125394775259843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938277722833859700346457 703708292125394775259843)
                      ·
                        rfl

theorem cell23_1370467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_1370467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370467 prefixEnd_1370467 := by exact prefixLift 1370467
  have htrace : WordTrace (prefixWord ++ tailWord_1370467) baseStart_1370467 baseEnd_1370467 := by
    simpa [prefixWord, tailWord_1370467, baseEnd_1370467] using wordTrace_append hprefix tailTrace_1370467
  have hstable : (prefixWord ++ tailWord_1370467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370467).length < 2 ^ (prefixWord ++ tailWord_1370467).sum := by decide
  have hdescent : baseEnd_1370467 < baseStart_1370467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370474 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1370474 : Nat := 118140960795 + 1370474 * 2 ^ 59
def prefixEnd_1370474 : Nat := 4983230072969 + 3 ^ 40 * 1370474 * 2
def baseEnd_1370474 : Nat := 703711886489976247872311

theorem tailTrace_1370474 : CollatzResearch.WordTrace tailWord_1370474 prefixEnd_1370474 703711886489976247872311 := by
  unfold tailWord_1370474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496323309253557792493619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33323528824676154113316317 12496323309253557792493619)
  ·
    refine ⟨18744484963880336688740429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12496323309253557792493619 18744484963880336688740429)
    ·
      refine ⟨7029181861455126258277661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18744484963880336688740429 7029181861455126258277661)
      ·
        refine ⟨2635943198045672346854123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7029181861455126258277661 2635943198045672346854123)
        ·
          refine ⟨3953914797068508520281185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635943198045672346854123 3953914797068508520281185)
          ·
            refine ⟨2965436097801381390210889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3953914797068508520281185 2965436097801381390210889)
            ·
              refine ⟨2224077073351036042658167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965436097801381390210889 2224077073351036042658167)
              ·
                refine ⟨3336115610026554063987251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224077073351036042658167 3336115610026554063987251)
                ·
                  refine ⟨5004173415039831095980877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336115610026554063987251 5004173415039831095980877)
                  ·
                    refine ⟨1876565030639936660992829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5004173415039831095980877 1876565030639936660992829)
                    ·
                      refine ⟨703711886489976247872311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1876565030639936660992829 703711886489976247872311)
                      ·
                        rfl

theorem cell23_1370474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1370474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370474 prefixEnd_1370474 := by exact prefixLift 1370474
  have htrace : WordTrace (prefixWord ++ tailWord_1370474) baseStart_1370474 baseEnd_1370474 := by
    simpa [prefixWord, tailWord_1370474, baseEnd_1370474] using wordTrace_append hprefix tailTrace_1370474
  have hstable : (prefixWord ++ tailWord_1370474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370474).length < 2 ^ (prefixWord ++ tailWord_1370474).sum := by decide
  have hdescent : baseEnd_1370474 < baseStart_1370474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370500 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1370500 : Nat := 118140960795 + 1370500 * 2 ^ 59
def prefixEnd_1370500 : Nat := 4983230072969 + 3 ^ 40 * 1370500 * 2
def baseEnd_1370500 : Nat := 703725236986993146147191

theorem tailTrace_1370500 : CollatzResearch.WordTrace tailWord_1370500 prefixEnd_1370500 703725236986993146147191 := by
  unfold tailWord_1370500
  simp only [CollatzResearch.WordTrace]
  refine ⟨24993120767460018805210477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33324161023280025073613969 24993120767460018805210477)
  ·
    refine ⟨9372420287797507051953929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24993120767460018805210477 9372420287797507051953929)
    ·
      refine ⟨7029315215848130288965447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9372420287797507051953929 7029315215848130288965447)
      ·
        refine ⟨10543972823772195433448171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029315215848130288965447 10543972823772195433448171)
        ·
          refine ⟨15815959235658293150172257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543972823772195433448171 15815959235658293150172257)
          ·
            refine ⟨11861969426743719862629193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15815959235658293150172257 11861969426743719862629193)
            ·
              refine ⟨8896477070057789896971895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11861969426743719862629193 8896477070057789896971895)
              ·
                refine ⟨13344715605086684845457843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8896477070057789896971895 13344715605086684845457843)
                ·
                  refine ⟨20017073407630027268186765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13344715605086684845457843 20017073407630027268186765)
                  ·
                    refine ⟨7506402527861260225570037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20017073407630027268186765 7506402527861260225570037)
                    ·
                      refine ⟨703725236986993146147191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7506402527861260225570037 703725236986993146147191)
                      ·
                        rfl

theorem cell23_1370500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1370500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370500 prefixEnd_1370500 := by exact prefixLift 1370500
  have htrace : WordTrace (prefixWord ++ tailWord_1370500) baseStart_1370500 baseEnd_1370500 := by
    simpa [prefixWord, tailWord_1370500, baseEnd_1370500] using wordTrace_append hprefix tailTrace_1370500
  have hstable : (prefixWord ++ tailWord_1370500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370500).length < 2 ^ (prefixWord ++ tailWord_1370500).sum := by decide
  have hdescent : baseEnd_1370500 < baseStart_1370500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370560 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1370560 : Nat := 118140960795 + 1370560 * 2 ^ 59
def prefixEnd_1370560 : Nat := 4983230072969 + 3 ^ 40 * 1370560 * 2
def baseEnd_1370560 : Nat := 703756045826262911396915

theorem tailTrace_1370560 : CollatzResearch.WordTrace tailWord_1370560 prefixEnd_1370560 703756045826262911396915 := by
  unfold tailWord_1370560
  simp only [CollatzResearch.WordTrace]
  refine ⟨24994214957351333928802567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33325619943135111905070089 24994214957351333928802567)
  ·
    refine ⟨37491322436027000893203851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24994214957351333928802567 37491322436027000893203851)
    ·
      refine ⟨56236983654040501339805777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37491322436027000893203851 56236983654040501339805777)
      ·
        refine ⟨42177737740530376004854333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56236983654040501339805777 42177737740530376004854333)
        ·
          refine ⟨15816651652698891001820375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42177737740530376004854333 15816651652698891001820375)
          ·
            refine ⟨23724977479048336502730563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15816651652698891001820375 23724977479048336502730563)
            ·
              refine ⟨35587466218572504754095845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23724977479048336502730563 35587466218572504754095845)
              ·
                refine ⟨6672649915982344641392971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35587466218572504754095845 6672649915982344641392971)
                ·
                  refine ⟨10008974873973516962089457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6672649915982344641392971 10008974873973516962089457)
                  ·
                    refine ⟨7506731155480137721567093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10008974873973516962089457 7506731155480137721567093)
                    ·
                      refine ⟨703756045826262911396915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7506731155480137721567093 703756045826262911396915)
                      ·
                        rfl

theorem cell23_1370560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1370560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370560 prefixEnd_1370560 := by exact prefixLift 1370560
  have htrace : WordTrace (prefixWord ++ tailWord_1370560) baseStart_1370560 baseEnd_1370560 := by
    simpa [prefixWord, tailWord_1370560, baseEnd_1370560] using wordTrace_append hprefix tailTrace_1370560
  have hstable : (prefixWord ++ tailWord_1370560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370560).length < 2 ^ (prefixWord ++ tailWord_1370560).sum := by decide
  have hdescent : baseEnd_1370560 < baseStart_1370560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370567 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1370567 : Nat := 118140960795 + 1370567 * 2 ^ 59
def prefixEnd_1370567 : Nat := 4983230072969 + 3 ^ 40 * 1370567 * 2
def baseEnd_1370567 : Nat := 234586546730281461336461

theorem tailTrace_1370567 : CollatzResearch.WordTrace tailWord_1370567 prefixEnd_1370567 234586546730281461336461 := by
  unfold tailWord_1370567
  simp only [CollatzResearch.WordTrace]
  refine ⟨49988685225677308053109955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33325790150451538702073303 49988685225677308053109955)
  ·
    refine ⟨74983027838515962079664933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49988685225677308053109955 74983027838515962079664933)
    ·
      refine ⟨14059317719721742889937175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74983027838515962079664933 14059317719721742889937175)
      ·
        refine ⟨21088976579582614334905763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14059317719721742889937175 21088976579582614334905763)
        ·
          refine ⟨31633464869373921502358645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21088976579582614334905763 31633464869373921502358645)
          ·
            refine ⟨2965637331503805140846123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31633464869373921502358645 2965637331503805140846123)
            ·
              refine ⟨4448455997255707711269185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2965637331503805140846123 4448455997255707711269185)
              ·
                refine ⟨3336341997941780783451889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4448455997255707711269185 3336341997941780783451889)
                ·
                  refine ⟨2502256498456335587588917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3336341997941780783451889 2502256498456335587588917)
                  ·
                    refine ⟨234586546730281461336461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2502256498456335587588917 234586546730281461336461)
                    ·
                      rfl

theorem cell23_1370567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1370567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370567 prefixEnd_1370567 := by exact prefixLift 1370567
  have htrace : WordTrace (prefixWord ++ tailWord_1370567) baseStart_1370567 baseEnd_1370567 := by
    simpa [prefixWord, tailWord_1370567, baseEnd_1370567] using wordTrace_append hprefix tailTrace_1370567
  have hstable : (prefixWord ++ tailWord_1370567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370567).length < 2 ^ (prefixWord ++ tailWord_1370567).sum := by decide
  have hdescent : baseEnd_1370567 < baseStart_1370567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370627 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 6]
def baseStart_1370627 : Nat := 118140960795 + 1370627 * 2 ^ 59
def prefixEnd_1370627 : Nat := 4983230072969 + 3 ^ 40 * 1370627 * 2
def baseEnd_1370627 : Nat := 78198938781123794362123

theorem tailTrace_1370627 : CollatzResearch.WordTrace tailWord_1370627 prefixEnd_1370627 78198938781123794362123 := by
  unfold tailWord_1370627
  simp only [CollatzResearch.WordTrace]
  refine ⟨49990873605459938300294135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33327249070306625533529423 49990873605459938300294135)
  ·
    refine ⟨74986310408189907450441203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49990873605459938300294135 74986310408189907450441203)
    ·
      refine ⟨112479465612284861175661805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74986310408189907450441203 112479465612284861175661805)
      ·
        refine ⟨42179799604606822940873177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112479465612284861175661805 42179799604606822940873177)
        ·
          refine ⟨31634849703455117205654883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42179799604606822940873177 31634849703455117205654883)
          ·
            refine ⟨47452274555182675808482325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31634849703455117205654883 47452274555182675808482325)
            ·
              refine ⟨2224325369774187928522609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47452274555182675808482325 2224325369774187928522609)
              ·
                refine ⟨1668244027330640946391957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224325369774187928522609 1668244027330640946391957)
                ·
                  refine ⟨78198938781123794362123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1668244027330640946391957 78198938781123794362123)
                  ·
                    rfl

theorem cell23_1370627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 6].length) (baseStart_1370627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370627 prefixEnd_1370627 := by exact prefixLift 1370627
  have htrace : WordTrace (prefixWord ++ tailWord_1370627) baseStart_1370627 baseEnd_1370627 := by
    simpa [prefixWord, tailWord_1370627, baseEnd_1370627] using wordTrace_append hprefix tailTrace_1370627
  have hstable : (prefixWord ++ tailWord_1370627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370627).length < 2 ^ (prefixWord ++ tailWord_1370627).sum := by decide
  have hdescent : baseEnd_1370627 < baseStart_1370627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370657 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1370657 : Nat := 118140960795 + 1370657 * 2 ^ 59
def prefixEnd_1370657 : Nat := 4983230072969 + 3 ^ 40 * 1370657 * 2
def baseEnd_1370657 : Nat := 234601951149916343961323

theorem tailTrace_1370657 : CollatzResearch.WordTrace tailWord_1370657 prefixEnd_1370657 234601951149916343961323 := by
  unfold tailWord_1370657
  simp only [CollatzResearch.WordTrace]
  refine ⟨49991967795351253423886225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33327978530234168949257483 49991967795351253423886225)
  ·
    refine ⟨37493975846513440067914669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49991967795351253423886225 37493975846513440067914669)
    ·
      refine ⟨14060240942442540025468001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37493975846513440067914669 14060240942442540025468001)
      ·
        refine ⟨10545180706831905019101001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14060240942442540025468001 10545180706831905019101001)
        ·
          refine ⟨7908885530123928764325751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10545180706831905019101001 7908885530123928764325751)
          ·
            refine ⟨11863328295185893146488627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7908885530123928764325751 11863328295185893146488627)
            ·
              refine ⟨17794992442778839719732941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863328295185893146488627 17794992442778839719732941)
              ·
                refine ⟨6673122166042064894899853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17794992442778839719732941 6673122166042064894899853)
                ·
                  refine ⟨2502420812265774335587445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6673122166042064894899853 2502420812265774335587445)
                  ·
                    refine ⟨234601951149916343961323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2502420812265774335587445 234601951149916343961323)
                    ·
                      rfl

theorem cell23_1370657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1370657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370657 prefixEnd_1370657 := by exact prefixLift 1370657
  have htrace : WordTrace (prefixWord ++ tailWord_1370657) baseStart_1370657 baseEnd_1370657 := by
    simpa [prefixWord, tailWord_1370657, baseEnd_1370657] using wordTrace_append hprefix tailTrace_1370657
  have hstable : (prefixWord ++ tailWord_1370657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370657).length < 2 ^ (prefixWord ++ tailWord_1370657).sum := by decide
  have hdescent : baseEnd_1370657 < baseStart_1370657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370711 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_1370711 : Nat := 118140960795 + 1370711 * 2 ^ 59
def prefixEnd_1370711 : Nat := 4983230072969 + 3 ^ 40 * 1370711 * 2
def baseEnd_1370711 : Nat := 703833581405091820608721

theorem tailTrace_1370711 : CollatzResearch.WordTrace tailWord_1370711 prefixEnd_1370711 703833581405091820608721 := by
  unfold tailWord_1370711
  simp only [CollatzResearch.WordTrace]
  refine ⟨49993937337155620646351987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33329291558103747097567991 49993937337155620646351987)
  ·
    refine ⟨74990906005733430969527981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49993937337155620646351987 74990906005733430969527981)
    ·
      refine ⟨28121589752150036613572993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74990906005733430969527981 28121589752150036613572993)
      ·
        refine ⟨21091192314112527460179745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28121589752150036613572993 21091192314112527460179745)
        ·
          refine ⟨15818394235584395595134809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21091192314112527460179745 15818394235584395595134809)
          ·
            refine ⟨11863795676688296696351107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15818394235584395595134809 11863795676688296696351107)
            ·
              refine ⟨17795693515032445044526661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11863795676688296696351107 17795693515032445044526661)
              ·
                refine ⟨3336692534068583445848749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17795693515032445044526661 3336692534068583445848749)
                ·
                  refine ⟨1251259700275718792193281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3336692534068583445848749 1251259700275718792193281)
                  ·
                    refine ⟨938444775206789094144961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1251259700275718792193281 938444775206789094144961)
                    ·
                      refine ⟨703833581405091820608721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938444775206789094144961 703833581405091820608721)
                      ·
                        rfl

theorem cell23_1370711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_1370711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370711 prefixEnd_1370711 := by exact prefixLift 1370711
  have htrace : WordTrace (prefixWord ++ tailWord_1370711) baseStart_1370711 baseEnd_1370711 := by
    simpa [prefixWord, tailWord_1370711, baseEnd_1370711] using wordTrace_append hprefix tailTrace_1370711
  have hstable : (prefixWord ++ tailWord_1370711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370711).length < 2 ^ (prefixWord ++ tailWord_1370711).sum := by decide
  have hdescent : baseEnd_1370711 < baseStart_1370711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370734 : List Nat := [4, 1, 2, 2, 2, 3, 9]
def baseStart_1370734 : Nat := 118140960795 + 1370734 * 2 ^ 59
def prefixEnd_1370734 : Nat := 4983230072969 + 3 ^ 40 * 1370734 * 2
def baseEnd_1370734 : Nat := 8689449277285743587915

theorem tailTrace_1370734 : CollatzResearch.WordTrace tailWord_1370734 prefixEnd_1370734 8689449277285743587915 := by
  unfold tailWord_1370734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249347027009036946804907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33329850810714863716292837 6249347027009036946804907)
  ·
    refine ⟨9374020540513555420207361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6249347027009036946804907 9374020540513555420207361)
    ·
      refine ⟨7030515405385166565155521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9374020540513555420207361 7030515405385166565155521)
      ·
        refine ⟨5272886554038874923866641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7030515405385166565155521 5272886554038874923866641)
        ·
          refine ⟨3954664915529156192899981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5272886554038874923866641 3954664915529156192899981)
          ·
            refine ⟨1482999343323433572337493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3954664915529156192899981 1482999343323433572337493)
            ·
              refine ⟨8689449277285743587915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1482999343323433572337493 8689449277285743587915)
              ·
                rfl

theorem cell23_1370734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 9].length) (baseStart_1370734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370734 prefixEnd_1370734 := by exact prefixLift 1370734
  have htrace : WordTrace (prefixWord ++ tailWord_1370734) baseStart_1370734 baseEnd_1370734 := by
    simpa [prefixWord, tailWord_1370734, baseEnd_1370734] using wordTrace_append hprefix tailTrace_1370734
  have hstable : (prefixWord ++ tailWord_1370734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370734).length < 2 ^ (prefixWord ++ tailWord_1370734).sum := by decide
  have hdescent : baseEnd_1370734 < baseStart_1370734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370767 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_1370767 : Nat := 118140960795 + 1370767 * 2 ^ 59
def prefixEnd_1370767 : Nat := 4983230072969 + 3 ^ 40 * 1370767 * 2
def baseEnd_1370767 : Nat := 703862336321743601508463

theorem tailTrace_1370767 : CollatzResearch.WordTrace tailWord_1370767 prefixEnd_1370767 703862336321743601508463 := by
  unfold tailWord_1370767
  simp only [CollatzResearch.WordTrace]
  refine ⟨49995979824952742210390555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33330653216635161473593703 49995979824952742210390555)
  ·
    refine ⟨74993969737429113315585833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49995979824952742210390555 74993969737429113315585833)
    ·
      refine ⟨56245477303071834986689375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74993969737429113315585833 56245477303071834986689375)
      ·
        refine ⟨84368215954607752480034063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56245477303071834986689375 84368215954607752480034063)
        ·
          refine ⟨126552323931911628720051095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84368215954607752480034063 126552323931911628720051095)
          ·
            refine ⟨189828485897867443080076643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126552323931911628720051095 189828485897867443080076643)
            ·
              refine ⟨284742728846801164620114965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189828485897867443080076643 284742728846801164620114965)
              ·
                refine ⟨13347315414693804591567889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284742728846801164620114965 13347315414693804591567889)
                ·
                  refine ⟨10010486561020353443675917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13347315414693804591567889 10010486561020353443675917)
                  ·
                    refine ⟨3753932460382632541378469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10010486561020353443675917 3753932460382632541378469)
                    ·
                      refine ⟨703862336321743601508463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3753932460382632541378469 703862336321743601508463)
                      ·
                        rfl

theorem cell23_1370767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_1370767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370767 prefixEnd_1370767 := by exact prefixLift 1370767
  have htrace : WordTrace (prefixWord ++ tailWord_1370767) baseStart_1370767 baseEnd_1370767 := by
    simpa [prefixWord, tailWord_1370767, baseEnd_1370767] using wordTrace_append hprefix tailTrace_1370767
  have hstable : (prefixWord ++ tailWord_1370767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370767).length < 2 ^ (prefixWord ++ tailWord_1370767).sum := by decide
  have hdescent : baseEnd_1370767 < baseStart_1370767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370778 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1370778 : Nat := 118140960795 + 1370778 * 2 ^ 59
def prefixEnd_1370778 : Nat := 4983230072969 + 3 ^ 40 * 1370778 * 2
def baseEnd_1370778 : Nat := 703867984608943058470913

theorem tailTrace_1370778 : CollatzResearch.WordTrace tailWord_1370778 prefixEnd_1370778 703867984608943058470913 := by
  unfold tailWord_1370778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499095256978222772260247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33330920685275260726027325 12499095256978222772260247)
  ·
    refine ⟨18748642885467334158390371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12499095256978222772260247 18748642885467334158390371)
    ·
      refine ⟨28122964328201001237585557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18748642885467334158390371 28122964328201001237585557)
      ·
        refine ⟨1318263952884421933011823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28122964328201001237585557 1318263952884421933011823)
        ·
          refine ⟨1977395929326632899517735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318263952884421933011823 1977395929326632899517735)
          ·
            refine ⟨2966093893989949349276603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977395929326632899517735 2966093893989949349276603)
            ·
              refine ⟨4449140840984924023914905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966093893989949349276603 4449140840984924023914905)
              ·
                refine ⟨3336855630738693017936179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449140840984924023914905 3336855630738693017936179)
                ·
                  refine ⟨5005283446108039526904269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3336855630738693017936179 5005283446108039526904269)
                  ·
                    refine ⟨1876981292290514822589101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5005283446108039526904269 1876981292290514822589101)
                    ·
                      refine ⟨703867984608943058470913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1876981292290514822589101 703867984608943058470913)
                      ·
                        rfl

theorem cell23_1370778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1370778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370778 prefixEnd_1370778 := by exact prefixLift 1370778
  have htrace : WordTrace (prefixWord ++ tailWord_1370778) baseStart_1370778 baseEnd_1370778 := by
    simpa [prefixWord, tailWord_1370778, baseEnd_1370778] using wordTrace_append hprefix tailTrace_1370778
  have hstable : (prefixWord ++ tailWord_1370778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370778).length < 2 ^ (prefixWord ++ tailWord_1370778).sum := by decide
  have hdescent : baseEnd_1370778 < baseStart_1370778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370787 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1370787 : Nat := 118140960795 + 1370787 * 2 ^ 59
def prefixEnd_1370787 : Nat := 4983230072969 + 3 ^ 40 * 1370787 * 2
def baseEnd_1370787 : Nat := 703872605934833523258371

theorem tailTrace_1370787 : CollatzResearch.WordTrace tailWord_1370787 prefixEnd_1370787 703872605934833523258371 := by
  unfold tailWord_1370787
  simp only [CollatzResearch.WordTrace]
  refine ⟨49996709284880285626118615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33331139523253523750745743 49996709284880285626118615)
  ·
    refine ⟨74995063927320428439177923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49996709284880285626118615 74995063927320428439177923)
    ·
      refine ⟨112492595890980642658766885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74995063927320428439177923 112492595890980642658766885)
      ·
        refine ⟨21092361729558870498518791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112492595890980642658766885 21092361729558870498518791)
        ·
          refine ⟨31638542594338305747778187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21092361729558870498518791 31638542594338305747778187)
          ·
            refine ⟨47457813891507458621667281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31638542594338305747778187 47457813891507458621667281)
            ·
              refine ⟨35593360418630593966250461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47457813891507458621667281 35593360418630593966250461)
              ·
                refine ⟨13347510156986472737343923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35593360418630593966250461 13347510156986472737343923)
                ·
                  refine ⟨20021265235479709106015885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13347510156986472737343923 20021265235479709106015885)
                  ·
                    refine ⟨7507974463304890914755957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20021265235479709106015885 7507974463304890914755957)
                    ·
                      refine ⟨703872605934833523258371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7507974463304890914755957 703872605934833523258371)
                      ·
                        rfl

theorem cell23_1370787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1370787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370787 prefixEnd_1370787 := by exact prefixLift 1370787
  have htrace : WordTrace (prefixWord ++ tailWord_1370787) baseStart_1370787 baseEnd_1370787 := by
    simpa [prefixWord, tailWord_1370787, baseEnd_1370787] using wordTrace_append hprefix tailTrace_1370787
  have hstable : (prefixWord ++ tailWord_1370787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370787).length < 2 ^ (prefixWord ++ tailWord_1370787).sum := by decide
  have hdescent : baseEnd_1370787 < baseStart_1370787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370824 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 7]
def baseStart_1370824 : Nat := 118140960795 + 1370824 * 2 ^ 59
def prefixEnd_1370824 : Nat := 4983230072969 + 3 ^ 40 * 1370824 * 2
def baseEnd_1370824 : Nat := 78210178302116653166189

theorem tailTrace_1370824 : CollatzResearch.WordTrace tailWord_1370824 prefixEnd_1370824 78210178302116653166189 := by
  unfold tailWord_1370824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24999029392873120472607763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33332039190497493963477017 24999029392873120472607763)
  ·
    refine ⟨37498544089309680708911645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24999029392873120472607763 37498544089309680708911645)
    ·
      refine ⟨14061954033491130265841867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37498544089309680708911645 14061954033491130265841867)
      ·
        refine ⟨21092931050236695398762801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14061954033491130265841867 21092931050236695398762801)
        ·
          refine ⟨15819698287677521549072101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21092931050236695398762801 15819698287677521549072101)
          ·
            refine ⟨2966193428939535290451019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15819698287677521549072101 2966193428939535290451019)
            ·
              refine ⟨4449290143409302935676529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966193428939535290451019 4449290143409302935676529)
              ·
                refine ⟨3336967607556977201757397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4449290143409302935676529 3336967607556977201757397)
                ·
                  refine ⟨78210178302116653166189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3336967607556977201757397 78210178302116653166189)
                  ·
                    rfl

theorem cell23_1370824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_1370824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370824 prefixEnd_1370824 := by exact prefixLift 1370824
  have htrace : WordTrace (prefixWord ++ tailWord_1370824) baseStart_1370824 baseEnd_1370824 := by
    simpa [prefixWord, tailWord_1370824, baseEnd_1370824] using wordTrace_append hprefix tailTrace_1370824
  have hstable : (prefixWord ++ tailWord_1370824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370824).length < 2 ^ (prefixWord ++ tailWord_1370824).sum := by decide
  have hdescent : baseEnd_1370824 < baseStart_1370824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370841 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 5]
def baseStart_1370841 : Nat := 118140960795 + 1370841 * 2 ^ 59
def prefixEnd_1370841 : Nat := 4983230072969 + 3 ^ 40 * 1370841 * 2
def baseEnd_1370841 : Nat := 78211148210019590220347

theorem tailTrace_1370841 : CollatzResearch.WordTrace tailWord_1370841 prefixEnd_1370841 78211148210019590220347 := by
  unfold tailWord_1370841
  simp only [CollatzResearch.WordTrace]
  refine ⟨49998678826684652848584377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33332452551123101899056251 49998678826684652848584377)
  ·
    refine ⟨37499009120013489636438283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49998678826684652848584377 37499009120013489636438283)
    ·
      refine ⟨56248513680020234454657425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37499009120013489636438283 56248513680020234454657425)
      ·
        refine ⟨42186385260015175840993069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56248513680020234454657425 42186385260015175840993069)
        ·
          refine ⟨15819894472505690940372401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42186385260015175840993069 15819894472505690940372401)
          ·
            refine ⟨11864920854379268205279301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15819894472505690940372401 11864920854379268205279301)
            ·
              refine ⟨2224672660196112788489869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11864920854379268205279301 2224672660196112788489869)
              ·
                refine ⟨834252247573542295683701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2224672660196112788489869 834252247573542295683701)
                ·
                  refine ⟨78211148210019590220347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834252247573542295683701 78211148210019590220347)
                  ·
                    rfl

theorem cell23_1370841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 5].length) (baseStart_1370841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370841 prefixEnd_1370841 := by exact prefixLift 1370841
  have htrace : WordTrace (prefixWord ++ tailWord_1370841) baseStart_1370841 baseEnd_1370841 := by
    simpa [prefixWord, tailWord_1370841, baseEnd_1370841] using wordTrace_append hprefix tailTrace_1370841
  have hstable : (prefixWord ++ tailWord_1370841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370841).length < 2 ^ (prefixWord ++ tailWord_1370841).sum := by decide
  have hdescent : baseEnd_1370841 < baseStart_1370841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370851 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1370851 : Nat := 118140960795 + 1370851 * 2 ^ 59
def prefixEnd_1370851 : Nat := 4983230072969 + 3 ^ 40 * 1370851 * 2
def baseEnd_1370851 : Nat := 703905468696721272858077

theorem tailTrace_1370851 : CollatzResearch.WordTrace tailWord_1370851 prefixEnd_1370851 703905468696721272858077 := by
  unfold tailWord_1370851
  simp only [CollatzResearch.WordTrace]
  refine ⟨49999043556648424556448407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33332695704432283037632271 49999043556648424556448407)
  ·
    refine ⟨74998565334972636834672611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49999043556648424556448407 74998565334972636834672611)
    ·
      refine ⟨112497848002458955252008917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74998565334972636834672611 112497848002458955252008917)
      ·
        refine ⟨2636668312557631763718959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 112497848002458955252008917 2636668312557631763718959)
        ·
          refine ⟨3955002468836447645578439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2636668312557631763718959 3955002468836447645578439)
          ·
            refine ⟨5932503703254671468367659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955002468836447645578439 5932503703254671468367659)
            ·
              refine ⟨8898755554882007202551489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932503703254671468367659 8898755554882007202551489)
              ·
                refine ⟨6674066666161505401913617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8898755554882007202551489 6674066666161505401913617)
                ·
                  refine ⟨5005549999621129051435213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6674066666161505401913617 5005549999621129051435213)
                  ·
                    refine ⟨1877081249857923394288205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5005549999621129051435213 1877081249857923394288205)
                    ·
                      refine ⟨703905468696721272858077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1877081249857923394288205 703905468696721272858077)
                      ·
                        rfl

theorem cell23_1370851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1370851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370851 prefixEnd_1370851 := by exact prefixLift 1370851
  have htrace : WordTrace (prefixWord ++ tailWord_1370851) baseStart_1370851 baseEnd_1370851 := by
    simpa [prefixWord, tailWord_1370851, baseEnd_1370851] using wordTrace_append hprefix tailTrace_1370851
  have hstable : (prefixWord ++ tailWord_1370851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370851).length < 2 ^ (prefixWord ++ tailWord_1370851).sum := by decide
  have hdescent : baseEnd_1370851 < baseStart_1370851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370869 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_1370869 : Nat := 118140960795 + 1370869 * 2 ^ 59
def prefixEnd_1370869 : Nat := 4983230072969 + 3 ^ 40 * 1370869 * 2
def baseEnd_1370869 : Nat := 703914711348502202432995

theorem tailTrace_1370869 : CollatzResearch.WordTrace tailWord_1370869 prefixEnd_1370869 703914711348502202432995 := by
  unfold tailWord_1370869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49999700070583213630603661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33333133380388809087069107 49999700070583213630603661)
  ·
    refine ⟨18749887526468705111476373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49999700070583213630603661 18749887526468705111476373)
    ·
      refine ⟨878900977803220552100455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18749887526468705111476373 878900977803220552100455)
      ·
        refine ⟨1318351466704830828150683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878900977803220552100455 1318351466704830828150683)
        ·
          refine ⟨1977527200057246242226025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318351466704830828150683 1977527200057246242226025)
          ·
            refine ⟨1483145400042934681669519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1977527200057246242226025 1483145400042934681669519)
            ·
              refine ⟨2224718100064402022504279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483145400042934681669519 2224718100064402022504279)
              ·
                refine ⟨3337077150096603033756419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224718100064402022504279 3337077150096603033756419)
                ·
                  refine ⟨5005615725144904550634629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337077150096603033756419 5005615725144904550634629)
                  ·
                    refine ⟨938552948464669603243993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5005615725144904550634629 938552948464669603243993)
                    ·
                      refine ⟨703914711348502202432995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938552948464669603243993 703914711348502202432995)
                      ·
                        rfl

theorem cell23_1370869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_1370869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370869 prefixEnd_1370869 := by exact prefixLift 1370869
  have htrace : WordTrace (prefixWord ++ tailWord_1370869) baseStart_1370869 baseEnd_1370869 := by
    simpa [prefixWord, tailWord_1370869, baseEnd_1370869] using wordTrace_append hprefix tailTrace_1370869
  have hstable : (prefixWord ++ tailWord_1370869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370869).length < 2 ^ (prefixWord ++ tailWord_1370869).sum := by decide
  have hdescent : baseEnd_1370869 < baseStart_1370869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370874 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1370874 : Nat := 118140960795 + 1370874 * 2 ^ 59
def prefixEnd_1370874 : Nat := 4983230072969 + 3 ^ 40 * 1370874 * 2
def baseEnd_1370874 : Nat := 703917278751774682870471

theorem tailTrace_1370874 : CollatzResearch.WordTrace tailWord_1370874 prefixEnd_1370874 703917278751774682870471 := by
  unfold tailWord_1370874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499970608891274871133919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33333254957043399656357117 12499970608891274871133919)
  ·
    refine ⟨18749955913336912306700879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12499970608891274871133919 18749955913336912306700879)
    ·
      refine ⟨28124933870005368460051319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18749955913336912306700879 28124933870005368460051319)
      ·
        refine ⟨42187400805008052690076979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28124933870005368460051319 42187400805008052690076979)
        ·
          refine ⟨63281101207512079035115469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42187400805008052690076979 63281101207512079035115469)
          ·
            refine ⟨23730412952817029638168301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63281101207512079035115469 23730412952817029638168301)
            ·
              refine ⟨8898904857306386114313113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23730412952817029638168301 8898904857306386114313113)
              ·
                refine ⟨6674178642979789585734835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8898904857306386114313113 6674178642979789585734835)
                ·
                  refine ⟨10011267964469684378602253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6674178642979789585734835 10011267964469684378602253)
                  ·
                    refine ⟨3754225486676131641975845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10011267964469684378602253 3754225486676131641975845)
                    ·
                      refine ⟨703917278751774682870471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3754225486676131641975845 703917278751774682870471)
                      ·
                        rfl

theorem cell23_1370874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1370874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370874 prefixEnd_1370874 := by exact prefixLift 1370874
  have htrace : WordTrace (prefixWord ++ tailWord_1370874) baseStart_1370874 baseEnd_1370874 := by
    simpa [prefixWord, tailWord_1370874, baseEnd_1370874] using wordTrace_append hprefix tailTrace_1370874
  have hstable : (prefixWord ++ tailWord_1370874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370874).length < 2 ^ (prefixWord ++ tailWord_1370874).sum := by decide
  have hdescent : baseEnd_1370874 < baseStart_1370874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370884 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1370884 : Nat := 118140960795 + 1370884 * 2 ^ 59
def prefixEnd_1370884 : Nat := 4983230072969 + 3 ^ 40 * 1370884 * 2
def baseEnd_1370884 : Nat := 234640804519439881248475

theorem tailTrace_1370884 : CollatzResearch.WordTrace tailWord_1370884 prefixEnd_1370884 234640804519439881248475 := by
  unfold tailWord_1370884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25000123582764435596199853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33333498110352580794933137 25000123582764435596199853)
  ·
    refine ⟨9375046343536663348574945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25000123582764435596199853 9375046343536663348574945)
    ·
      refine ⟨7031284757652497511431209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9375046343536663348574945 7031284757652497511431209)
      ·
        refine ⟨5273463568239373133573407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7031284757652497511431209 5273463568239373133573407)
        ·
          refine ⟨7910195352359059700360111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5273463568239373133573407 7910195352359059700360111)
          ·
            refine ⟨11865293028538589550540167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910195352359059700360111 11865293028538589550540167)
            ·
              refine ⟨17797939542807884325810251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11865293028538589550540167 17797939542807884325810251)
              ·
                refine ⟨26696909314211826488715377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17797939542807884325810251 26696909314211826488715377)
                ·
                  refine ⟨20022681985658869866536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26696909314211826488715377 20022681985658869866536533)
                  ·
                    refine ⟨234640804519439881248475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20022681985658869866536533 234640804519439881248475)
                    ·
                      rfl

theorem cell23_1370884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1370884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370884 prefixEnd_1370884 := by exact prefixLift 1370884
  have htrace : WordTrace (prefixWord ++ tailWord_1370884) baseStart_1370884 baseEnd_1370884 := by
    simpa [prefixWord, tailWord_1370884, baseEnd_1370884] using wordTrace_append hprefix tailTrace_1370884
  have hstable : (prefixWord ++ tailWord_1370884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370884).length < 2 ^ (prefixWord ++ tailWord_1370884).sum := by decide
  have hdescent : baseEnd_1370884 < baseStart_1370884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370894 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1370894 : Nat := 118140960795 + 1370894 * 2 ^ 59
def prefixEnd_1370894 : Nat := 4983230072969 + 3 ^ 40 * 1370894 * 2
def baseEnd_1370894 : Nat := 703927548364864604620379

theorem tailTrace_1370894 : CollatzResearch.WordTrace tailWord_1370894 prefixEnd_1370894 703927548364864604620379 := by
  unfold tailWord_1370894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250076486936580362532967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33333741263661761933509157 6250076486936580362532967)
  ·
    refine ⟨9375114730404870543799451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6250076486936580362532967 9375114730404870543799451)
    ·
      refine ⟨14062672095607305815699177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9375114730404870543799451 14062672095607305815699177)
      ·
        refine ⟨10547004071705479361774383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14062672095607305815699177 10547004071705479361774383)
        ·
          refine ⟨15820506107558219042661575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10547004071705479361774383 15820506107558219042661575)
          ·
            refine ⟨23730759161337328563992363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15820506107558219042661575 23730759161337328563992363)
            ·
              refine ⟨35596138742005992845988545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23730759161337328563992363 35596138742005992845988545)
              ·
                refine ⟨26697104056504494634491409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35596138742005992845988545 26697104056504494634491409)
                ·
                  refine ⟨20022828042378370975868557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26697104056504494634491409 20022828042378370975868557)
                  ·
                    refine ⟨7508560515891889115950709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20022828042378370975868557 7508560515891889115950709)
                    ·
                      refine ⟨703927548364864604620379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7508560515891889115950709 703927548364864604620379)
                      ·
                        rfl

theorem cell23_1370894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1370894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370894 prefixEnd_1370894 := by exact prefixLift 1370894
  have htrace : WordTrace (prefixWord ++ tailWord_1370894) baseStart_1370894 baseEnd_1370894 := by
    simpa [prefixWord, tailWord_1370894, baseEnd_1370894] using wordTrace_append hprefix tailTrace_1370894
  have hstable : (prefixWord ++ tailWord_1370894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370894).length < 2 ^ (prefixWord ++ tailWord_1370894).sum := by decide
  have hdescent : baseEnd_1370894 < baseStart_1370894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370911 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1370911 : Nat := 118140960795 + 1370911 * 2 ^ 59
def prefixEnd_1370911 : Nat := 4983230072969 + 3 ^ 40 * 1370911 * 2
def baseEnd_1370911 : Nat := 703936277535991038107801

theorem tailTrace_1370911 : CollatzResearch.WordTrace tailWord_1370911 prefixEnd_1370911 703936277535991038107801 := by
  unfold tailWord_1370911
  simp only [CollatzResearch.WordTrace]
  refine ⟨50001231936431054803632587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33334154624287369869088391 50001231936431054803632587)
  ·
    refine ⟨75001847904646582205448881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50001231936431054803632587 75001847904646582205448881)
    ·
      refine ⟨56251385928484936654086661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75001847904646582205448881 56251385928484936654086661)
      ·
        refine ⟨10547134861590925622641249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56251385928484936654086661 10547134861590925622641249)
        ·
          refine ⟨7910351146193194216980937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10547134861590925622641249 7910351146193194216980937)
          ·
            refine ⟨5932763359644895662735703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7910351146193194216980937 5932763359644895662735703)
            ·
              refine ⟨8899145039467343494103555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5932763359644895662735703 8899145039467343494103555)
              ·
                refine ⟨13348717559201015241155333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8899145039467343494103555 13348717559201015241155333)
                ·
                  refine ⟨2502884542350190357716625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13348717559201015241155333 2502884542350190357716625)
                  ·
                    refine ⟨1877163406762642768287469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2502884542350190357716625 1877163406762642768287469)
                    ·
                      refine ⟨703936277535991038107801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1877163406762642768287469 703936277535991038107801)
                      ·
                        rfl

theorem cell23_1370911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1370911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370911 prefixEnd_1370911 := by exact prefixLift 1370911
  have htrace : WordTrace (prefixWord ++ tailWord_1370911) baseStart_1370911 baseEnd_1370911 := by
    simpa [prefixWord, tailWord_1370911, baseEnd_1370911] using wordTrace_append hprefix tailTrace_1370911
  have hstable : (prefixWord ++ tailWord_1370911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370911).length < 2 ^ (prefixWord ++ tailWord_1370911).sum := by decide
  have hdescent : baseEnd_1370911 < baseStart_1370911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370931 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 6]
def baseStart_1370931 : Nat := 118140960795 + 1370931 * 2 ^ 59
def prefixEnd_1370931 : Nat := 4983230072969 + 3 ^ 40 * 1370931 * 2
def baseEnd_1370931 : Nat := 78216283016564551095301

theorem tailTrace_1370931 : CollatzResearch.WordTrace tailWord_1370931 prefixEnd_1370931 78216283016564551095301 := by
  unfold tailWord_1370931
  simp only [CollatzResearch.WordTrace]
  refine ⟨50001961396358598219360647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33334640930905732146240431 50001961396358598219360647)
  ·
    refine ⟨75002942094537897329040971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50001961396358598219360647 75002942094537897329040971)
    ·
      refine ⟨112504413141806845993561457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75002942094537897329040971 112504413141806845993561457)
      ·
        refine ⟨84378309856355134495171093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112504413141806845993561457 84378309856355134495171093)
        ·
          refine ⟨3955233274516646929461145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84378309856355134495171093 3955233274516646929461145)
          ·
            refine ⟨2966424955887485197095859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955233274516646929461145 2966424955887485197095859)
            ·
              refine ⟨4449637433831227795643789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966424955887485197095859 4449637433831227795643789)
              ·
                refine ⟨1668614037686710423366421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4449637433831227795643789 1668614037686710423366421)
                ·
                  refine ⟨78216283016564551095301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1668614037686710423366421 78216283016564551095301)
                  ·
                    rfl

theorem cell23_1370931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 6].length) (baseStart_1370931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370931 prefixEnd_1370931 := by exact prefixLift 1370931
  have htrace : WordTrace (prefixWord ++ tailWord_1370931) baseStart_1370931 baseEnd_1370931 := by
    simpa [prefixWord, tailWord_1370931, baseEnd_1370931] using wordTrace_append hprefix tailTrace_1370931
  have hstable : (prefixWord ++ tailWord_1370931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370931).length < 2 ^ (prefixWord ++ tailWord_1370931).sum := by decide
  have hdescent : baseEnd_1370931 < baseStart_1370931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370954 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1370954 : Nat := 118140960795 + 1370954 * 2 ^ 59
def prefixEnd_1370954 : Nat := 4983230072969 + 3 ^ 40 * 1370954 * 2
def baseEnd_1370954 : Nat := 703958357204134369870103

theorem tailTrace_1370954 : CollatzResearch.WordTrace tailWord_1370954 prefixEnd_1370954 703958357204134369870103 := by
  unfold tailWord_1370954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12500700068818818286861979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33335200183516848764965277 12500700068818818286861979)
  ·
    refine ⟨18751050103228227430292969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12500700068818818286861979 18751050103228227430292969)
    ·
      refine ⟨14063287577421170572719727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18751050103228227430292969 14063287577421170572719727)
      ·
        refine ⟨21094931366131755859079591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063287577421170572719727 21094931366131755859079591)
        ·
          refine ⟨31642397049197633788619387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21094931366131755859079591 31642397049197633788619387)
          ·
            refine ⟨47463595573796450682929081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31642397049197633788619387 47463595573796450682929081)
            ·
              refine ⟨35597696680347338012196811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47463595573796450682929081 35597696680347338012196811)
              ·
                refine ⟨53396545020521007018295217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35597696680347338012196811 53396545020521007018295217)
                ·
                  refine ⟨40047408765390755263721413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53396545020521007018295217 40047408765390755263721413)
                  ·
                    refine ⟨7508889143510766611947765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40047408765390755263721413 7508889143510766611947765)
                    ·
                      refine ⟨703958357204134369870103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7508889143510766611947765 703958357204134369870103)
                      ·
                        rfl

theorem cell23_1370954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1370954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370954 prefixEnd_1370954 := by exact prefixLift 1370954
  have htrace : WordTrace (prefixWord ++ tailWord_1370954) baseStart_1370954 baseEnd_1370954 := by
    simpa [prefixWord, tailWord_1370954, baseEnd_1370954] using wordTrace_append hprefix tailTrace_1370954
  have hstable : (prefixWord ++ tailWord_1370954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370954).length < 2 ^ (prefixWord ++ tailWord_1370954).sum := by decide
  have hdescent : baseEnd_1370954 < baseStart_1370954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370975 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 1, 1, 3]
def baseStart_1370975 : Nat := 118140960795 + 1370975 * 2 ^ 59
def prefixEnd_1370975 : Nat := 4983230072969 + 3 ^ 40 * 1370975 * 2
def baseEnd_1370975 : Nat := 703969140297878787707507

theorem tailTrace_1370975 : CollatzResearch.WordTrace tailWord_1370975 prefixEnd_1370975 703969140297878787707507 := by
  unfold tailWord_1370975
  simp only [CollatzResearch.WordTrace]
  refine ⟨50003566208199193733962379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33335710805466129155974919 50003566208199193733962379)
  ·
    refine ⟨75005349312298790600943569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50003566208199193733962379 75005349312298790600943569)
    ·
      refine ⟨56254011984224092950707677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75005349312298790600943569 56254011984224092950707677)
      ·
        refine ⟨21095254494084034856515379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56254011984224092950707677 21095254494084034856515379)
        ·
          refine ⟨31642881741126052284773069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095254494084034856515379 31642881741126052284773069)
          ·
            refine ⟨11866080652922269606789901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31642881741126052284773069 11866080652922269606789901)
            ·
              refine ⟨4449780244845851102546213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11866080652922269606789901 4449780244845851102546213)
              ·
                refine ⟨834333795908597081727415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4449780244845851102546213 834333795908597081727415)
                ·
                  refine ⟨1251500693862895622591123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834333795908597081727415 1251500693862895622591123)
                  ·
                    refine ⟨1877251040794343433886685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1251500693862895622591123 1877251040794343433886685)
                    ·
                      refine ⟨703969140297878787707507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1877251040794343433886685 703969140297878787707507)
                      ·
                        rfl

theorem cell23_1370975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_1370975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370975 prefixEnd_1370975 := by exact prefixLift 1370975
  have htrace : WordTrace (prefixWord ++ tailWord_1370975) baseStart_1370975 baseEnd_1370975 := by
    simpa [prefixWord, tailWord_1370975, baseEnd_1370975] using wordTrace_append hprefix tailTrace_1370975
  have hstable : (prefixWord ++ tailWord_1370975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370975).length < 2 ^ (prefixWord ++ tailWord_1370975).sum := by decide
  have hdescent : baseEnd_1370975 < baseStart_1370975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1370981 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1370981 : Nat := 118140960795 + 1370981 * 2 ^ 59
def prefixEnd_1370981 : Nat := 4983230072969 + 3 ^ 40 * 1370981 * 2
def baseEnd_1370981 : Nat := 703972221181805764232479

theorem tailTrace_1370981 : CollatzResearch.WordTrace tailWord_1370981 prefixEnd_1370981 703972221181805764232479 := by
  unfold tailWord_1370981
  simp only [CollatzResearch.WordTrace]
  refine ⟨50003785046177456758680797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33335856697451637839120531 50003785046177456758680797)
  ·
    refine ⟨18751419392316546284505299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50003785046177456758680797 18751419392316546284505299)
    ·
      refine ⟨28127129088474819426757949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18751419392316546284505299 28127129088474819426757949)
      ·
        refine ⟨10547673408178057285034231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28127129088474819426757949 10547673408178057285034231)
        ·
          refine ⟨15821510112267085927551347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10547673408178057285034231 15821510112267085927551347)
          ·
            refine ⟨23732265168400628891327021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15821510112267085927551347 23732265168400628891327021)
            ·
              refine ⟨8899599438150235834247633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23732265168400628891327021 8899599438150235834247633)
              ·
                refine ⟨6674699578612676875685725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8899599438150235834247633 6674699578612676875685725)
                ·
                  refine ⟨2503012341979753828382147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6674699578612676875685725 2503012341979753828382147)
                  ·
                    refine ⟨3754518512969630742573221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503012341979753828382147 3754518512969630742573221)
                    ·
                      refine ⟨703972221181805764232479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3754518512969630742573221 703972221181805764232479)
                      ·
                        rfl

theorem cell23_1370981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1370981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1370981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1370981 prefixEnd_1370981 := by exact prefixLift 1370981
  have htrace : WordTrace (prefixWord ++ tailWord_1370981) baseStart_1370981 baseEnd_1370981 := by
    simpa [prefixWord, tailWord_1370981, baseEnd_1370981] using wordTrace_append hprefix tailTrace_1370981
  have hstable : (prefixWord ++ tailWord_1370981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1370981).length < 2 ^ (prefixWord ++ tailWord_1370981).sum := by decide
  have hdescent : baseEnd_1370981 < baseStart_1370981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1370981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371004 : List Nat := [2, 2, 2, 1, 1, 1, 1, 13]
def baseStart_1371004 : Nat := 118140960795 + 1371004 * 2 ^ 59
def prefixEnd_1371004 : Nat := 4983230072969 + 3 ^ 40 * 1371004 * 2
def baseEnd_1371004 : Nat := 26073482638402191638699

theorem tailTrace_1371004 : CollatzResearch.WordTrace tailWord_1371004 prefixEnd_1371004 26073482638402191638699 := by
  unfold tailWord_1371004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25002311962547065843384033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33336415950062754457845377 25002311962547065843384033)
  ·
    refine ⟨18751733971910299382538025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25002311962547065843384033 18751733971910299382538025)
    ·
      refine ⟨14063800478932724536903519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18751733971910299382538025 14063800478932724536903519)
      ·
        refine ⟨21095700718399086805355279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14063800478932724536903519 21095700718399086805355279)
        ·
          refine ⟨31643551077598630208032919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21095700718399086805355279 31643551077598630208032919)
          ·
            refine ⟨47465326616397945312049379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31643551077598630208032919 47465326616397945312049379)
            ·
              refine ⟨71197989924596917968074069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47465326616397945312049379 71197989924596917968074069)
              ·
                refine ⟨26073482638402191638699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 71197989924596917968074069 26073482638402191638699)
                ·
                  rfl

theorem cell23_1371004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 13].length) (baseStart_1371004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371004 prefixEnd_1371004 := by exact prefixLift 1371004
  have htrace : WordTrace (prefixWord ++ tailWord_1371004) baseStart_1371004 baseEnd_1371004 := by
    simpa [prefixWord, tailWord_1371004, baseEnd_1371004] using wordTrace_append hprefix tailTrace_1371004
  have hstable : (prefixWord ++ tailWord_1371004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371004).length < 2 ^ (prefixWord ++ tailWord_1371004).sum := by decide
  have hdescent : baseEnd_1371004 < baseStart_1371004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371011 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4]
def baseStart_1371011 : Nat := 118140960795 + 1371011 * 2 ^ 59
def prefixEnd_1371011 : Nat := 4983230072969 + 3 ^ 40 * 1371011 * 2
def baseEnd_1371011 : Nat := 703987625601440646857341

theorem tailTrace_1371011 : CollatzResearch.WordTrace tailWord_1371011 prefixEnd_1371011 703987625601440646857341 := by
  unfold tailWord_1371011
  simp only [CollatzResearch.WordTrace]
  refine ⟨50004879236068771882272887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33336586157379181254848591 50004879236068771882272887)
  ·
    refine ⟨75007318854103157823409331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50004879236068771882272887 75007318854103157823409331)
    ·
      refine ⟨112510978281154736735113997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75007318854103157823409331 112510978281154736735113997)
      ·
        refine ⟨42191616855433026275667749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112510978281154736735113997 42191616855433026275667749)
        ·
          refine ⟨7910928160393692426687703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42191616855433026275667749 7910928160393692426687703)
          ·
            refine ⟨11866392240590538640031555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7910928160393692426687703 11866392240590538640031555)
            ·
              refine ⟨17799588360885807960047333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11866392240590538640031555 17799588360885807960047333)
              ·
                refine ⟨3337422817666088992508875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17799588360885807960047333 3337422817666088992508875)
                ·
                  refine ⟨5006134226499133488763313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3337422817666088992508875 5006134226499133488763313)
                  ·
                    refine ⟨3754600669874350116572485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5006134226499133488763313 3754600669874350116572485)
                    ·
                      refine ⟨703987625601440646857341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3754600669874350116572485 703987625601440646857341)
                      ·
                        rfl

theorem cell23_1371011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_1371011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371011 prefixEnd_1371011 := by exact prefixLift 1371011
  have htrace : WordTrace (prefixWord ++ tailWord_1371011) baseStart_1371011 baseEnd_1371011 := by
    simpa [prefixWord, tailWord_1371011, baseEnd_1371011] using wordTrace_append hprefix tailTrace_1371011
  have hstable : (prefixWord ++ tailWord_1371011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371011).length < 2 ^ (prefixWord ++ tailWord_1371011).sum := by decide
  have hdescent : baseEnd_1371011 < baseStart_1371011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371015 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_1371015 : Nat := 118140960795 + 1371015 * 2 ^ 59
def prefixEnd_1371015 : Nat := 4983230072969 + 3 ^ 40 * 1371015 * 2
def baseEnd_1371015 : Nat := 703989679524058631207323

theorem tailTrace_1371015 : CollatzResearch.WordTrace tailWord_1371015 prefixEnd_1371015 703989679524058631207323 := by
  unfold tailWord_1371015
  simp only [CollatzResearch.WordTrace]
  refine ⟨50005025128054280565418499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33336683418702853710278999 50005025128054280565418499)
  ·
    refine ⟨75007537692081420848127749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50005025128054280565418499 75007537692081420848127749)
    ·
      refine ⟨14063913317265266409023953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75007537692081420848127749 14063913317265266409023953)
      ·
        refine ⟨10547934987948949806767965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14063913317265266409023953 10547934987948949806767965)
        ·
          refine ⟨3955475620480856177537987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10547934987948949806767965 3955475620480856177537987)
          ·
            refine ⟨5933213430721284266306981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3955475620480856177537987 5933213430721284266306981)
            ·
              refine ⟨1112477518260240799932559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5933213430721284266306981 1112477518260240799932559)
              ·
                refine ⟨1668716277390361199898839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112477518260240799932559 1668716277390361199898839)
                ·
                  refine ⟨2503074416085541799848259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668716277390361199898839 2503074416085541799848259)
                  ·
                    refine ⟨3754611624128312699772389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503074416085541799848259 3754611624128312699772389)
                    ·
                      refine ⟨703989679524058631207323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3754611624128312699772389 703989679524058631207323)
                      ·
                        rfl

theorem cell23_1371015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_1371015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371015 prefixEnd_1371015 := by exact prefixLift 1371015
  have htrace : WordTrace (prefixWord ++ tailWord_1371015) baseStart_1371015 baseEnd_1371015 := by
    simpa [prefixWord, tailWord_1371015, baseEnd_1371015] using wordTrace_append hprefix tailTrace_1371015
  have hstable : (prefixWord ++ tailWord_1371015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371015).length < 2 ^ (prefixWord ++ tailWord_1371015).sum := by decide
  have hdescent : baseEnd_1371015 < baseStart_1371015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371042 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1371042 : Nat := 118140960795 + 1371042 * 2 ^ 59
def prefixEnd_1371042 : Nat := 4983230072969 + 3 ^ 40 * 1371042 * 2
def baseEnd_1371042 : Nat := 234667847833910008523233

theorem tailTrace_1371042 : CollatzResearch.WordTrace tailWord_1371042 prefixEnd_1371042 234667847833910008523233 := by
  unfold tailWord_1371042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501502474739116044162845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33337339932637642784434253 12501502474739116044162845)
  ·
    refine ⟨4688063428027168516561067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12501502474739116044162845 4688063428027168516561067)
    ·
      refine ⟨7032095142040752774841601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4688063428027168516561067 7032095142040752774841601)
      ·
        refine ⟨5274071356530564581131201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7032095142040752774841601 5274071356530564581131201)
        ·
          refine ⟨3955553517397923435848401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5274071356530564581131201 3955553517397923435848401)
          ·
            refine ⟨2966665138048442576886301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955553517397923435848401 2966665138048442576886301)
            ·
              refine ⟨1112499426768165966332363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2966665138048442576886301 1112499426768165966332363)
              ·
                refine ⟨1668749140152248949498545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112499426768165966332363 1668749140152248949498545)
                ·
                  refine ⟨1251561855114186712123909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668749140152248949498545 1251561855114186712123909)
                  ·
                    refine ⟨234667847833910008523233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251561855114186712123909 234667847833910008523233)
                    ·
                      rfl

theorem cell23_1371042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1371042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371042 prefixEnd_1371042 := by exact prefixLift 1371042
  have htrace : WordTrace (prefixWord ++ tailWord_1371042) baseStart_1371042 baseEnd_1371042 := by
    simpa [prefixWord, tailWord_1371042, baseEnd_1371042] using wordTrace_append hprefix tailTrace_1371042
  have hstable : (prefixWord ++ tailWord_1371042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371042).length < 2 ^ (prefixWord ++ tailWord_1371042).sum := by decide
  have hdescent : baseEnd_1371042 < baseStart_1371042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371061 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1371061 : Nat := 118140960795 + 1371061 * 2 ^ 59
def prefixEnd_1371061 : Nat := 4983230072969 + 3 ^ 40 * 1371061 * 2
def baseEnd_1371061 : Nat := 704013299634165451232111

theorem tailTrace_1371061 : CollatzResearch.WordTrace tailWord_1371061 prefixEnd_1371061 704013299634165451232111 := by
  unfold tailWord_1371061
  simp only [CollatzResearch.WordTrace]
  refine ⟨50006702885887630421593037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33337801923925086947728691 50006702885887630421593037)
  ·
    refine ⟨18752513582207861408097389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50006702885887630421593037 18752513582207861408097389)
    ·
      refine ⟨7032192593327948028036521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18752513582207861408097389 7032192593327948028036521)
      ·
        refine ⟨5274144444995961021027391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7032192593327948028036521 5274144444995961021027391)
        ·
          refine ⟨7911216667493941531541087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274144444995961021027391 7911216667493941531541087)
          ·
            refine ⟨11866825001240912297311631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911216667493941531541087 11866825001240912297311631)
            ·
              refine ⟨17800237501861368445967447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11866825001240912297311631 17800237501861368445967447)
              ·
                refine ⟨26700356252792052668951171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17800237501861368445967447 26700356252792052668951171)
                ·
                  refine ⟨40050534379188079003426757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26700356252792052668951171 40050534379188079003426757)
                  ·
                    refine ⟨7509475196097764813142517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40050534379188079003426757 7509475196097764813142517)
                    ·
                      refine ⟨704013299634165451232111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7509475196097764813142517 704013299634165451232111)
                      ·
                        rfl

theorem cell23_1371061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1371061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371061 prefixEnd_1371061 := by exact prefixLift 1371061
  have htrace : WordTrace (prefixWord ++ tailWord_1371061) baseStart_1371061 baseEnd_1371061 := by
    simpa [prefixWord, tailWord_1371061, baseEnd_1371061] using wordTrace_append hprefix tailTrace_1371061
  have hstable : (prefixWord ++ tailWord_1371061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371061).length < 2 ^ (prefixWord ++ tailWord_1371061).sum := by decide
  have hdescent : baseEnd_1371061 < baseStart_1371061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371128 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 5]
def baseStart_1371128 : Nat := 118140960795 + 1371128 * 2 ^ 59
def prefixEnd_1371128 : Nat := 4983230072969 + 3 ^ 40 * 1371128 * 2
def baseEnd_1371128 : Nat := 78227522537557409899367

theorem tailTrace_1371128 : CollatzResearch.WordTrace tailWord_1371128 prefixEnd_1371128 78227522537557409899367 := by
  unfold tailWord_1371128
  simp only [CollatzResearch.WordTrace]
  refine ⟨25004573288322450432141019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33339431051096600576188025 25004573288322450432141019)
  ·
    refine ⟨37506859932483675648211529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25004573288322450432141019 37506859932483675648211529)
    ·
      refine ⟨28130144949362756736158647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37506859932483675648211529 28130144949362756736158647)
      ·
        refine ⟨42195217424044135104237971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28130144949362756736158647 42195217424044135104237971)
        ·
          refine ⟨63292826136066202656356957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42195217424044135104237971 63292826136066202656356957)
          ·
            refine ⟨23734809801024825996133859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63292826136066202656356957 23734809801024825996133859)
            ·
              refine ⟨35602214701537238994200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23734809801024825996133859 35602214701537238994200789)
              ·
                refine ⟨834426907067279038926581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35602214701537238994200789 834426907067279038926581)
                ·
                  refine ⟨78227522537557409899367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834426907067279038926581 78227522537557409899367)
                  ·
                    rfl

theorem cell23_1371128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 5].length) (baseStart_1371128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371128 prefixEnd_1371128 := by exact prefixLift 1371128
  have htrace : WordTrace (prefixWord ++ tailWord_1371128) baseStart_1371128 baseEnd_1371128 := by
    simpa [prefixWord, tailWord_1371128, baseEnd_1371128] using wordTrace_append hprefix tailTrace_1371128
  have hstable : (prefixWord ++ tailWord_1371128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371128).length < 2 ^ (prefixWord ++ tailWord_1371128).sum := by decide
  have hdescent : baseEnd_1371128 < baseStart_1371128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371175 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1371175 : Nat := 118140960795 + 1371175 * 2 ^ 59
def prefixEnd_1371175 : Nat := 4983230072969 + 3 ^ 40 * 1371175 * 2
def baseEnd_1371175 : Nat := 234690612142926001735529

theorem tailTrace_1371175 : CollatzResearch.WordTrace tailWord_1371175 prefixEnd_1371175 234690612142926001735529 := by
  unfold tailWord_1371175
  simp only [CollatzResearch.WordTrace]
  refine ⟨50010860807474627891242979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33340573871649751927495319 50010860807474627891242979)
  ·
    refine ⟨75016291211211941836864469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50010860807474627891242979 75016291211211941836864469)
    ·
      refine ⟨1758194325262779886801511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 75016291211211941836864469 1758194325262779886801511)
      ·
        refine ⟨2637291487894169830202267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758194325262779886801511 2637291487894169830202267)
        ·
          refine ⟨3955937231841254745303401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637291487894169830202267 3955937231841254745303401)
          ·
            refine ⟨2966952923880941058977551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955937231841254745303401 2966952923880941058977551)
            ·
              refine ⟨4450429385821411588466327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966952923880941058977551 4450429385821411588466327)
              ·
                refine ⟨6675644078732117382699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4450429385821411588466327 6675644078732117382699491)
                ·
                  refine ⟨10013466118098176074049237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6675644078732117382699491 10013466118098176074049237)
                  ·
                    refine ⟨234690612142926001735529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10013466118098176074049237 234690612142926001735529)
                    ·
                      rfl

theorem cell23_1371175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1371175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371175 prefixEnd_1371175 := by exact prefixLift 1371175
  have htrace : WordTrace (prefixWord ++ tailWord_1371175) baseStart_1371175 baseEnd_1371175 := by
    simpa [prefixWord, tailWord_1371175, baseEnd_1371175] using wordTrace_append hprefix tailTrace_1371175
  have hstable : (prefixWord ++ tailWord_1371175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371175).length < 2 ^ (prefixWord ++ tailWord_1371175).sum := by decide
  have hdescent : baseEnd_1371175 < baseStart_1371175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371239 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1371239 : Nat := 118140960795 + 1371239 * 2 ^ 59
def prefixEnd_1371239 : Nat := 4983230072969 + 3 ^ 40 * 1371239 * 2
def baseEnd_1371239 : Nat := 234701566396888584935431

theorem tailTrace_1371239 : CollatzResearch.WordTrace tailWord_1371239 prefixEnd_1371239 234701566396888584935431 := by
  unfold tailWord_1371239
  simp only [CollatzResearch.WordTrace]
  refine ⟨50013195079242766821572771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33342130052828511214381847 50013195079242766821572771)
  ·
    refine ⟨75019792618864150232359157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50013195079242766821572771 75019792618864150232359157)
    ·
      refine ⟨7033105558018514084283671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75019792618864150232359157 7033105558018514084283671)
      ·
        refine ⟨10549658337027771126425507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7033105558018514084283671 10549658337027771126425507)
        ·
          refine ⟨15824487505541656689638261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10549658337027771126425507 15824487505541656689638261)
          ·
            refine ⟨1483545703644530314653587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15824487505541656689638261 1483545703644530314653587)
            ·
              refine ⟨2225318555466795471980381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483545703644530314653587 2225318555466795471980381)
              ·
                refine ⟨834494458300048301992643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2225318555466795471980381 834494458300048301992643)
                ·
                  refine ⟨1251741687450072452988965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834494458300048301992643 1251741687450072452988965)
                  ·
                    refine ⟨234701566396888584935431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251741687450072452988965 234701566396888584935431)
                    ·
                      rfl

theorem cell23_1371239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1371239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371239 prefixEnd_1371239 := by exact prefixLift 1371239
  have htrace : WordTrace (prefixWord ++ tailWord_1371239) baseStart_1371239 baseEnd_1371239 := by
    simpa [prefixWord, tailWord_1371239, baseEnd_1371239] using wordTrace_append hprefix tailTrace_1371239
  have hstable : (prefixWord ++ tailWord_1371239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371239).length < 2 ^ (prefixWord ++ tailWord_1371239).sum := by decide
  have hdescent : baseEnd_1371239 < baseStart_1371239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371269 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 6]
def baseStart_1371269 : Nat := 118140960795 + 1371269 * 2 ^ 59
def prefixEnd_1371269 : Nat := 4983230072969 + 3 ^ 40 * 1371269 * 2
def baseEnd_1371269 : Nat := 78235567067811181936795

theorem tailTrace_1371269 : CollatzResearch.WordTrace tailWord_1371269 prefixEnd_1371269 78235567067811181936795 := by
  unfold tailWord_1371269
  simp only [CollatzResearch.WordTrace]
  refine ⟨50014289269134081945164861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33342859512756054630109907 50014289269134081945164861)
  ·
    refine ⟨18755358475925280729436823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50014289269134081945164861 18755358475925280729436823)
    ·
      refine ⟨28133037713887921094155235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18755358475925280729436823 28133037713887921094155235)
      ·
        refine ⟨42199556570831881641232853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28133037713887921094155235 42199556570831881641232853)
        ·
          refine ⟨989052107128872225966395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42199556570831881641232853 989052107128872225966395)
          ·
            refine ⟨1483578160693308338949593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989052107128872225966395 1483578160693308338949593)
            ·
              refine ⟨1112683620519981254212195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483578160693308338949593 1112683620519981254212195)
              ·
                refine ⟨1669025430779971881318293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112683620519981254212195 1669025430779971881318293)
                ·
                  refine ⟨78235567067811181936795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1669025430779971881318293 78235567067811181936795)
                  ·
                    rfl

theorem cell23_1371269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_1371269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371269 prefixEnd_1371269 := by exact prefixLift 1371269
  have htrace : WordTrace (prefixWord ++ tailWord_1371269) baseStart_1371269 baseEnd_1371269 := by
    simpa [prefixWord, tailWord_1371269, baseEnd_1371269] using wordTrace_append hprefix tailTrace_1371269
  have hstable : (prefixWord ++ tailWord_1371269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371269).length < 2 ^ (prefixWord ++ tailWord_1371269).sum := by decide
  have hdescent : baseEnd_1371269 < baseStart_1371269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371282 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1371282 : Nat := 118140960795 + 1371282 * 2 ^ 59
def prefixEnd_1371282 : Nat := 4983230072969 + 3 ^ 40 * 1371282 * 2
def baseEnd_1371282 : Nat := 234708926286269695522865

theorem tailTrace_1371282 : CollatzResearch.WordTrace tailWord_1371282 prefixEnd_1371282 234708926286269695522865 := by
  unfold tailWord_1371282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12503690854521746291347025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33343175612057990110258733 12503690854521746291347025)
  ·
    refine ⟨9377768140891309718510269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12503690854521746291347025 9377768140891309718510269)
    ·
      refine ⟨3516663052834241144441351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9377768140891309718510269 3516663052834241144441351)
      ·
        refine ⟨5274994579251361716662027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3516663052834241144441351 5274994579251361716662027)
        ·
          refine ⟨7912491868877042574993041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274994579251361716662027 7912491868877042574993041)
          ·
            refine ⟨5934368901657781931244781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7912491868877042574993041 5934368901657781931244781)
            ·
              refine ⟨2225388338121668224216793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5934368901657781931244781 2225388338121668224216793)
              ·
                refine ⟨1669041253591251168162595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225388338121668224216793 1669041253591251168162595)
                ·
                  refine ⟨2503561880386876752243893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669041253591251168162595 2503561880386876752243893)
                  ·
                    refine ⟨234708926286269695522865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2503561880386876752243893 234708926286269695522865)
                    ·
                      rfl

theorem cell23_1371282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1371282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371282 prefixEnd_1371282 := by exact prefixLift 1371282
  have htrace : WordTrace (prefixWord ++ tailWord_1371282) baseStart_1371282 baseEnd_1371282 := by
    simpa [prefixWord, tailWord_1371282, baseEnd_1371282] using wordTrace_append hprefix tailTrace_1371282
  have hstable : (prefixWord ++ tailWord_1371282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371282).length < 2 ^ (prefixWord ++ tailWord_1371282).sum := by decide
  have hdescent : baseEnd_1371282 < baseStart_1371282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371285 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_1371285 : Nat := 118140960795 + 1371285 * 2 ^ 59
def prefixEnd_1371285 : Nat := 4983230072969 + 3 ^ 40 * 1371285 * 2
def baseEnd_1371285 : Nat := 704128319300772574831081

theorem tailTrace_1371285 : CollatzResearch.WordTrace tailWord_1371285 prefixEnd_1371285 704128319300772574831081 := by
  unfold tailWord_1371285
  simp only [CollatzResearch.WordTrace]
  refine ⟨50014872837076116677747309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33343248558050744451831539 50014872837076116677747309)
  ·
    refine ⟨18755577313903543754155241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50014872837076116677747309 18755577313903543754155241)
    ·
      refine ⟨14066682985427657815616431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18755577313903543754155241 14066682985427657815616431)
      ·
        refine ⟨21100024478141486723424647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14066682985427657815616431 21100024478141486723424647)
        ·
          refine ⟨31650036717212230085136971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21100024478141486723424647 31650036717212230085136971)
          ·
            refine ⟨47475055075818345127705457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31650036717212230085136971 47475055075818345127705457)
            ·
              refine ⟨35606291306863758845779093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47475055075818345127705457 35606291306863758845779093)
              ·
                refine ⟨1669044905009238695895895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35606291306863758845779093 1669044905009238695895895)
                ·
                  refine ⟨2503567357513858043843843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669044905009238695895895 2503567357513858043843843)
                  ·
                    refine ⟨3755351036270787065765765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503567357513858043843843 3755351036270787065765765)
                    ·
                      refine ⟨704128319300772574831081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3755351036270787065765765 704128319300772574831081)
                      ·
                        rfl

theorem cell23_1371285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_1371285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371285 prefixEnd_1371285 := by exact prefixLift 1371285
  have htrace : WordTrace (prefixWord ++ tailWord_1371285) baseStart_1371285 baseEnd_1371285 := by
    simpa [prefixWord, tailWord_1371285, baseEnd_1371285] using wordTrace_append hprefix tailTrace_1371285
  have hstable : (prefixWord ++ tailWord_1371285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371285).length < 2 ^ (prefixWord ++ tailWord_1371285).sum := by decide
  have hdescent : baseEnd_1371285 < baseStart_1371285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371313 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1371313 : Nat := 118140960795 + 1371313 * 2 ^ 59
def prefixEnd_1371313 : Nat := 4983230072969 + 3 ^ 40 * 1371313 * 2
def baseEnd_1371313 : Nat := 704142696759098465280953

theorem tailTrace_1371313 : CollatzResearch.WordTrace tailWord_1371313 prefixEnd_1371313 704142696759098465280953 := by
  unfold tailWord_1371313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50015894080974677459766593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33343929387316451639844395 50015894080974677459766593)
  ·
    refine ⟨37511920560731008094824945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50015894080974677459766593 37511920560731008094824945)
    ·
      refine ⟨28133940420548256071118709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37511920560731008094824945 28133940420548256071118709)
      ·
        refine ⟨2637556914426399006667379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28133940420548256071118709 2637556914426399006667379)
        ·
          refine ⟨3956335371639598510001069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637556914426399006667379 3956335371639598510001069)
          ·
            refine ⟨1483625764364849441250401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3956335371639598510001069 1483625764364849441250401)
            ·
              refine ⟨1112719323273637080937801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483625764364849441250401 1112719323273637080937801)
              ·
                refine ⟨834539492455227810703351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112719323273637080937801 834539492455227810703351)
                ·
                  refine ⟨1251809238682841716055027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834539492455227810703351 1251809238682841716055027)
                  ·
                    refine ⟨1877713858024262574082541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1251809238682841716055027 1877713858024262574082541)
                    ·
                      refine ⟨704142696759098465280953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1877713858024262574082541 704142696759098465280953)
                      ·
                        rfl

theorem cell23_1371313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1371313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371313 prefixEnd_1371313 := by exact prefixLift 1371313
  have htrace : WordTrace (prefixWord ++ tailWord_1371313) baseStart_1371313 baseEnd_1371313 := by
    simpa [prefixWord, tailWord_1371313, baseEnd_1371313] using wordTrace_append hprefix tailTrace_1371313
  have hstable : (prefixWord ++ tailWord_1371313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371313).length < 2 ^ (prefixWord ++ tailWord_1371313).sum := by decide
  have hdescent : baseEnd_1371313 < baseStart_1371313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371329 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1371329 : Nat := 118140960795 + 1371329 * 2 ^ 59
def prefixEnd_1371329 : Nat := 4983230072969 + 3 ^ 40 * 1371329 * 2
def baseEnd_1371329 : Nat := 234716970816523467560293

theorem tailTrace_1371329 : CollatzResearch.WordTrace tailWord_1371329 prefixEnd_1371329 234716970816523467560293 := by
  unfold tailWord_1371329
  simp only [CollatzResearch.WordTrace]
  refine ⟨50016477648916712192349041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33344318432611141461566027 50016477648916712192349041)
  ·
    refine ⟨37512358236687534144261781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50016477648916712192349041 37512358236687534144261781)
    ·
      refine ⟨1758391792344728163012271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37512358236687534144261781 1758391792344728163012271)
      ·
        refine ⟨2637587688517092244518407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758391792344728163012271 2637587688517092244518407)
        ·
          refine ⟨3956381532775638366777611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637587688517092244518407 3956381532775638366777611)
          ·
            refine ⟨5934572299163457550166417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956381532775638366777611 5934572299163457550166417)
            ·
              refine ⟨4450929224372593162624813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5934572299163457550166417 4450929224372593162624813)
              ·
                refine ⟨1669098459139722435984305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4450929224372593162624813 1669098459139722435984305)
                ·
                  refine ⟨1251823844354791826988229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669098459139722435984305 1251823844354791826988229)
                  ·
                    refine ⟨234716970816523467560293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251823844354791826988229 234716970816523467560293)
                    ·
                      rfl

theorem cell23_1371329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1371329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371329 prefixEnd_1371329 := by exact prefixLift 1371329
  have htrace : WordTrace (prefixWord ++ tailWord_1371329) baseStart_1371329 baseEnd_1371329 := by
    simpa [prefixWord, tailWord_1371329, baseEnd_1371329] using wordTrace_append hprefix tailTrace_1371329
  have hstable : (prefixWord ++ tailWord_1371329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371329).length < 2 ^ (prefixWord ++ tailWord_1371329).sum := by decide
  have hdescent : baseEnd_1371329 < baseStart_1371329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371342 : List Nat := [4, 1, 1, 1, 5, 1, 3, 7]
def baseStart_1371342 : Nat := 118140960795 + 1371342 * 2 ^ 59
def prefixEnd_1371342 : Nat := 4983230072969 + 3 ^ 40 * 1371342 * 2
def baseEnd_1371342 : Nat := 26079910655484401919197

theorem tailTrace_1371342 : CollatzResearch.WordTrace tailWord_1371342 prefixEnd_1371342 26079910655484401919197 := by
  unfold tailWord_1371342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252118974733701926571535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33344634531913076941714853 6252118974733701926571535)
  ·
    refine ⟨9378178462100552889857303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6252118974733701926571535 9378178462100552889857303)
    ·
      refine ⟨14067267693150829334785955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9378178462100552889857303 14067267693150829334785955)
      ·
        refine ⟨21100901539726244002178933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14067267693150829334785955 21100901539726244002178933)
        ·
          refine ⟨1978209519349335375204275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21100901539726244002178933 1978209519349335375204275)
          ·
            refine ⟨2967314279024003062806413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978209519349335375204275 2967314279024003062806413)
            ·
              refine ⟨1112742854634001148552405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2967314279024003062806413 1112742854634001148552405)
              ·
                refine ⟨26079910655484401919197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1112742854634001148552405 26079910655484401919197)
                ·
                  rfl

theorem cell23_1371342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_1371342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371342 prefixEnd_1371342 := by exact prefixLift 1371342
  have htrace : WordTrace (prefixWord ++ tailWord_1371342) baseStart_1371342 baseEnd_1371342 := by
    simpa [prefixWord, tailWord_1371342, baseEnd_1371342] using wordTrace_append hprefix tailTrace_1371342
  have hstable : (prefixWord ++ tailWord_1371342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371342).length < 2 ^ (prefixWord ++ tailWord_1371342).sum := by decide
  have hdescent : baseEnd_1371342 < baseStart_1371342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371380 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1371380 : Nat := 118140960795 + 1371380 * 2 ^ 59
def prefixEnd_1371380 : Nat := 4983230072969 + 3 ^ 40 * 1371380 * 2
def baseEnd_1371380 : Nat := 234725699987649901047715

theorem tailTrace_1371380 : CollatzResearch.WordTrace tailWord_1371380 prefixEnd_1371380 234725699987649901047715 := by
  unfold tailWord_1371380
  simp only [CollatzResearch.WordTrace]
  refine ⟨25009168885865973951227797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33345558514487965268303729 25009168885865973951227797)
  ·
    refine ⟨1172304791524967528963803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25009168885865973951227797 1172304791524967528963803)
    ·
      refine ⟨1758457187287451293445705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172304791524967528963803 1758457187287451293445705)
      ·
        refine ⟨1318842890465588470084279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1758457187287451293445705 1318842890465588470084279)
        ·
          refine ⟨1978264335698382705126419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318842890465588470084279 1978264335698382705126419)
          ·
            refine ⟨2967396503547574057689629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978264335698382705126419 2967396503547574057689629)
            ·
              refine ⟨1112773688830340271633611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2967396503547574057689629 1112773688830340271633611)
              ·
                refine ⟨1669160533245510407450417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112773688830340271633611 1669160533245510407450417)
                ·
                  refine ⟨1251870399934132805587813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669160533245510407450417 1251870399934132805587813)
                  ·
                    refine ⟨234725699987649901047715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1251870399934132805587813 234725699987649901047715)
                    ·
                      rfl

theorem cell23_1371380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1371380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371380 prefixEnd_1371380 := by exact prefixLift 1371380
  have htrace : WordTrace (prefixWord ++ tailWord_1371380) baseStart_1371380 baseEnd_1371380 := by
    simpa [prefixWord, tailWord_1371380, baseEnd_1371380] using wordTrace_append hprefix tailTrace_1371380
  have hstable : (prefixWord ++ tailWord_1371380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371380).length < 2 ^ (prefixWord ++ tailWord_1371380).sum := by decide
  have hdescent : baseEnd_1371380 < baseStart_1371380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371396 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_1371396 : Nat := 118140960795 + 1371396 * 2 ^ 59
def prefixEnd_1371396 : Nat := 4983230072969 + 3 ^ 40 * 1371396 * 2
def baseEnd_1371396 : Nat := 704185315653421640543071

theorem tailTrace_1371396 : CollatzResearch.WordTrace tailWord_1371396 prefixEnd_1371396 704185315653421640543071 := by
  unfold tailWord_1371396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25009460669836991317519021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33345947559782655090025361 25009460669836991317519021)
  ·
    refine ⟨9378547751188871744069633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25009460669836991317519021 9378547751188871744069633)
    ·
      refine ⟨7033910813391653808052225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9378547751188871744069633 7033910813391653808052225)
      ·
        refine ⟨5275433110043740356039169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7033910813391653808052225 5275433110043740356039169)
        ·
          refine ⟨3956574832532805267029377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275433110043740356039169 3956574832532805267029377)
          ·
            refine ⟨2967431124399603950272033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3956574832532805267029377 2967431124399603950272033)
            ·
              refine ⟨2225573343299702962704025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2967431124399603950272033 2225573343299702962704025)
              ·
                refine ⟨1669180007474777222028019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225573343299702962704025 1669180007474777222028019)
                ·
                  refine ⟨2503770011212165833042029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669180007474777222028019 2503770011212165833042029)
                  ·
                    refine ⟨938913754204562187390761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503770011212165833042029 938913754204562187390761)
                    ·
                      refine ⟨704185315653421640543071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938913754204562187390761 704185315653421640543071)
                      ·
                        rfl

theorem cell23_1371396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_1371396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371396 prefixEnd_1371396 := by exact prefixLift 1371396
  have htrace : WordTrace (prefixWord ++ tailWord_1371396) baseStart_1371396 baseEnd_1371396 := by
    simpa [prefixWord, tailWord_1371396, baseEnd_1371396] using wordTrace_append hprefix tailTrace_1371396
  have hstable : (prefixWord ++ tailWord_1371396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371396).length < 2 ^ (prefixWord ++ tailWord_1371396).sum := by decide
  have hdescent : baseEnd_1371396 < baseStart_1371396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371432 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 7]
def baseStart_1371432 : Nat := 118140960795 + 1371432 * 2 ^ 59
def prefixEnd_1371432 : Nat := 4983230072969 + 3 ^ 40 * 1371432 * 2
def baseEnd_1371432 : Nat := 78244866772998166632545

theorem tailTrace_1371432 : CollatzResearch.WordTrace tailWord_1371432 prefixEnd_1371432 78244866772998166632545 := by
  unfold tailWord_1371432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25010117183771780391674275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33346822911695707188899033 25010117183771780391674275)
  ·
    refine ⟨37515175775657670587511413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25010117183771780391674275 37515175775657670587511413)
    ·
      refine ⟨3517047728967906617579195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37515175775657670587511413 3517047728967906617579195)
      ·
        refine ⟨5275571593451859926368793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517047728967906617579195 5275571593451859926368793)
        ·
          refine ⟨3956678695088894944776595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5275571593451859926368793 3956678695088894944776595)
          ·
            refine ⟨5935018042633342417164893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3956678695088894944776595 5935018042633342417164893)
            ·
              refine ⟨2225631765987503406436835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5935018042633342417164893 2225631765987503406436835)
              ·
                refine ⟨3338447648981255109655253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225631765987503406436835 3338447648981255109655253)
                ·
                  refine ⟨78244866772998166632545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3338447648981255109655253 78244866772998166632545)
                  ·
                    rfl

theorem cell23_1371432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_1371432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371432 prefixEnd_1371432 := by exact prefixLift 1371432
  have htrace : WordTrace (prefixWord ++ tailWord_1371432) baseStart_1371432 baseEnd_1371432 := by
    simpa [prefixWord, tailWord_1371432, baseEnd_1371432] using wordTrace_append hprefix tailTrace_1371432
  have hstable : (prefixWord ++ tailWord_1371432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371432).length < 2 ^ (prefixWord ++ tailWord_1371432).sum := by decide
  have hdescent : baseEnd_1371432 < baseStart_1371432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371443 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 2, 2, 2]
def baseStart_1371443 : Nat := 118140960795 + 1371443 * 2 ^ 59
def prefixEnd_1371443 : Nat := 4983230072969 + 3 ^ 40 * 1371443 * 2
def baseEnd_1371443 : Nat := 704209449244182956655355

theorem tailTrace_1371443 : CollatzResearch.WordTrace tailWord_1371443 prefixEnd_1371443 704209449244182956655355 := by
  unfold tailWord_1371443
  simp only [CollatzResearch.WordTrace]
  refine ⟨50020635570503709661998983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33347090380335806441332655 50020635570503709661998983)
  ·
    refine ⟨75030953355755564492998475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50020635570503709661998983 75030953355755564492998475)
    ·
      refine ⟨112546430033633346739497713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75030953355755564492998475 112546430033633346739497713)
      ·
        refine ⟨84409822525225010054623285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112546430033633346739497713 84409822525225010054623285)
        ·
          refine ⟨7913420861739844692620933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84409822525225010054623285 7913420861739844692620933)
          ·
            refine ⟨1483766411576220879866425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7913420861739844692620933 1483766411576220879866425)
            ·
              refine ⟨1112824808682165659899819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483766411576220879866425 1112824808682165659899819)
              ·
                refine ⟨1669237213023248489849729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112824808682165659899819 1669237213023248489849729)
                ·
                  refine ⟨1251927909767436367387297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669237213023248489849729 1251927909767436367387297)
                  ·
                    refine ⟨938945932325577275540473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1251927909767436367387297 938945932325577275540473)
                    ·
                      refine ⟨704209449244182956655355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 938945932325577275540473 704209449244182956655355)
                      ·
                        rfl

theorem cell23_1371443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 2, 2, 2].length) (baseStart_1371443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371443 prefixEnd_1371443 := by exact prefixLift 1371443
  have htrace : WordTrace (prefixWord ++ tailWord_1371443) baseStart_1371443 baseEnd_1371443 := by
    simpa [prefixWord, tailWord_1371443, baseEnd_1371443] using wordTrace_append hprefix tailTrace_1371443
  have hstable : (prefixWord ++ tailWord_1371443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371443).length < 2 ^ (prefixWord ++ tailWord_1371443).sum := by decide
  have hdescent : baseEnd_1371443 < baseStart_1371443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371465 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_1371465 : Nat := 118140960795 + 1371465 * 2 ^ 59
def prefixEnd_1371465 : Nat := 4983230072969 + 3 ^ 40 * 1371465 * 2
def baseEnd_1371465 : Nat := 704220745818581870580253

theorem tailTrace_1371465 : CollatzResearch.WordTrace tailWord_1371465 prefixEnd_1371465 704220745818581870580253 := by
  unfold tailWord_1371465
  simp only [CollatzResearch.WordTrace]
  refine ⟨50021437976424007419299849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33347625317616004946199899 50021437976424007419299849)
  ·
    refine ⟨37516078482318005564474887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50021437976424007419299849 37516078482318005564474887)
    ·
      refine ⟨56274117723477008346712331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37516078482318005564474887 56274117723477008346712331)
      ·
        refine ⟨84411176585215512520068497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56274117723477008346712331 84411176585215512520068497)
        ·
          refine ⟨63308382438911634390051373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84411176585215512520068497 63308382438911634390051373)
          ·
            refine ⟨23740643414591862896269265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63308382438911634390051373 23740643414591862896269265)
            ·
              refine ⟨17805482560943897172201949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23740643414591862896269265 17805482560943897172201949)
              ·
                refine ⟨6677055960353961439575731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17805482560943897172201949 6677055960353961439575731)
                ·
                  refine ⟨10015583940530942159363597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6677055960353961439575731 10015583940530942159363597)
                  ·
                    refine ⟨3755843977699103309761349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10015583940530942159363597 3755843977699103309761349)
                    ·
                      refine ⟨704220745818581870580253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3755843977699103309761349 704220745818581870580253)
                      ·
                        rfl

theorem cell23_1371465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_1371465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371465 prefixEnd_1371465 := by exact prefixLift 1371465
  have htrace : WordTrace (prefixWord ++ tailWord_1371465) baseStart_1371465 baseEnd_1371465 := by
    simpa [prefixWord, tailWord_1371465, baseEnd_1371465] using wordTrace_append hprefix tailTrace_1371465
  have hstable : (prefixWord ++ tailWord_1371465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371465).length < 2 ^ (prefixWord ++ tailWord_1371465).sum := by decide
  have hdescent : baseEnd_1371465 < baseStart_1371465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371482 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1371482 : Nat := 118140960795 + 1371482 * 2 ^ 59
def prefixEnd_1371482 : Nat := 4983230072969 + 3 ^ 40 * 1371482 * 2
def baseEnd_1371482 : Nat := 704229474989708304067675

theorem tailTrace_1371482 : CollatzResearch.WordTrace tailWord_1371482 prefixEnd_1371482 704229474989708304067675 := by
  unfold tailWord_1371482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505514504340604830667175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33348038678241612881779133 12505514504340604830667175)
  ·
    refine ⟨18758271756510907246000763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12505514504340604830667175 18758271756510907246000763)
    ·
      refine ⟨28137407634766360869001145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18758271756510907246000763 28137407634766360869001145)
      ·
        refine ⟨21103055726074770651750859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28137407634766360869001145 21103055726074770651750859)
        ·
          refine ⟨31654583589112155977626289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21103055726074770651750859 31654583589112155977626289)
          ·
            refine ⟨23740937691834116983219717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31654583589112155977626289 23740937691834116983219717)
            ·
              refine ⟨4451425817218896934353697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23740937691834116983219717 4451425817218896934353697)
              ·
                refine ⟨3338569362914172700765273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4451425817218896934353697 3338569362914172700765273)
                ·
                  refine ⟨2503927022185629525573955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3338569362914172700765273 2503927022185629525573955)
                  ·
                    refine ⟨3755890533278444288360933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2503927022185629525573955 3755890533278444288360933)
                    ·
                      refine ⟨704229474989708304067675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3755890533278444288360933 704229474989708304067675)
                      ·
                        rfl

theorem cell23_1371482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1371482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371482 prefixEnd_1371482 := by exact prefixLift 1371482
  have htrace : WordTrace (prefixWord ++ tailWord_1371482) baseStart_1371482 baseEnd_1371482 := by
    simpa [prefixWord, tailWord_1371482, baseEnd_1371482] using wordTrace_append hprefix tailTrace_1371482
  have hstable : (prefixWord ++ tailWord_1371482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371482).length < 2 ^ (prefixWord ++ tailWord_1371482).sum := by decide
  have hdescent : baseEnd_1371482 < baseStart_1371482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371559 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1371559 : Nat := 118140960795 + 1371559 * 2 ^ 59
def prefixEnd_1371559 : Nat := 4983230072969 + 3 ^ 40 * 1371559 * 2
def baseEnd_1371559 : Nat := 704269013000104502804821

theorem tailTrace_1371559 : CollatzResearch.WordTrace tailWord_1371559 prefixEnd_1371559 704269013000104502804821 := by
  unfold tailWord_1371559
  simp only [CollatzResearch.WordTrace]
  refine ⟨50024866438083461473221731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33349910958722307648814487 50024866438083461473221731)
  ·
    refine ⟨75037299657125192209832597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50024866438083461473221731 75037299657125192209832597)
    ·
      refine ⟨3517373421427743384835903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 75037299657125192209832597 3517373421427743384835903)
      ·
        refine ⟨5276060132141615077253855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517373421427743384835903 5276060132141615077253855)
        ·
          refine ⟨7914090198212422615880783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276060132141615077253855 7914090198212422615880783)
          ·
            refine ⟨11871135297318633923821175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914090198212422615880783 11871135297318633923821175)
            ·
              refine ⟨17806702945977950885731763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871135297318633923821175 17806702945977950885731763)
              ·
                refine ⟨26710054418966926328597645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17806702945977950885731763 26710054418966926328597645)
                ·
                  refine ⟨10016270407112597373224117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26710054418966926328597645 10016270407112597373224117)
                  ·
                    refine ⟨939025350666806003739761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10016270407112597373224117 939025350666806003739761)
                    ·
                      refine ⟨704269013000104502804821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939025350666806003739761 704269013000104502804821)
                      ·
                        rfl

theorem cell23_1371559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1371559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371559 prefixEnd_1371559 := by exact prefixLift 1371559
  have htrace : WordTrace (prefixWord ++ tailWord_1371559) baseStart_1371559 baseEnd_1371559 := by
    simpa [prefixWord, tailWord_1371559, baseEnd_1371559] using wordTrace_append hprefix tailTrace_1371559
  have hstable : (prefixWord ++ tailWord_1371559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371559).length < 2 ^ (prefixWord ++ tailWord_1371559).sum := by decide
  have hdescent : baseEnd_1371559 < baseStart_1371559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371569 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 1, 5]
def baseStart_1371569 : Nat := 118140960795 + 1371569 * 2 ^ 59
def prefixEnd_1371569 : Nat := 4983230072969 + 3 ^ 40 * 1371569 * 2
def baseEnd_1371569 : Nat := 234758049268883154559925

theorem tailTrace_1371569 : CollatzResearch.WordTrace tailWord_1371569 prefixEnd_1371569 234758049268883154559925 := by
  unfold tailWord_1371569
  simp only [CollatzResearch.WordTrace]
  refine ⟨50025231168047233181085761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33350154112031488787390507 50025231168047233181085761)
  ·
    refine ⟨37518923376035424885814321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50025231168047233181085761 37518923376035424885814321)
    ·
      refine ⟨28139192532026568664360741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37518923376035424885814321 28139192532026568664360741)
      ·
        refine ⟨5276098599754981624567639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28139192532026568664360741 5276098599754981624567639)
        ·
          refine ⟨7914147899632472436851459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276098599754981624567639 7914147899632472436851459)
          ·
            refine ⟨11871221849448708655277189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914147899632472436851459 11871221849448708655277189)
            ·
              refine ⟨2225854096771632872864473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11871221849448708655277189 2225854096771632872864473)
              ·
                refine ⟨1669390572578724654648355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225854096771632872864473 1669390572578724654648355)
                ·
                  refine ⟨2504085858868086981972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669390572578724654648355 2504085858868086981972533)
                  ·
                    refine ⟨234758049268883154559925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2504085858868086981972533 234758049268883154559925)
                    ·
                      rfl

theorem cell23_1371569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_1371569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371569 prefixEnd_1371569 := by exact prefixLift 1371569
  have htrace : WordTrace (prefixWord ++ tailWord_1371569) baseStart_1371569 baseEnd_1371569 := by
    simpa [prefixWord, tailWord_1371569, baseEnd_1371569] using wordTrace_append hprefix tailTrace_1371569
  have hstable : (prefixWord ++ tailWord_1371569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371569).length < 2 ^ (prefixWord ++ tailWord_1371569).sum := by decide
  have hdescent : baseEnd_1371569 < baseStart_1371569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371582 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1371582 : Nat := 118140960795 + 1371582 * 2 ^ 59
def prefixEnd_1371582 : Nat := 4983230072969 + 3 ^ 40 * 1371582 * 2
def baseEnd_1371582 : Nat := 234760274351719304272405

theorem tailTrace_1371582 : CollatzResearch.WordTrace tailWord_1371582 prefixEnd_1371582 234760274351719304272405 := by
  unfold tailWord_1371582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253213164625017050163625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33350470211333424267539333 6253213164625017050163625)
  ·
    refine ⟨4689909873468762787622719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6253213164625017050163625 4689909873468762787622719)
    ·
      refine ⟨7034864810203144181434079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4689909873468762787622719 7034864810203144181434079)
      ·
        refine ⟨10552297215304716272151119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7034864810203144181434079 10552297215304716272151119)
        ·
          refine ⟨15828445822957074408226679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552297215304716272151119 15828445822957074408226679)
          ·
            refine ⟨23742668734435611612340019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15828445822957074408226679 23742668734435611612340019)
            ·
              refine ⟨35614003101653417418510029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23742668734435611612340019 35614003101653417418510029)
              ·
                refine ⟨13355251163120031531941261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35614003101653417418510029 13355251163120031531941261)
                ·
                  refine ⟨5008219186170011824477973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13355251163120031531941261 5008219186170011824477973)
                  ·
                    refine ⟨234760274351719304272405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5008219186170011824477973 234760274351719304272405)
                    ·
                      rfl

theorem cell23_1371582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1371582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371582 prefixEnd_1371582 := by exact prefixLift 1371582
  have htrace : WordTrace (prefixWord ++ tailWord_1371582) baseStart_1371582 baseEnd_1371582 := by
    simpa [prefixWord, tailWord_1371582, baseEnd_1371582] using wordTrace_append hprefix tailTrace_1371582
  have hstable : (prefixWord ++ tailWord_1371582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371582).length < 2 ^ (prefixWord ++ tailWord_1371582).sum := by decide
  have hdescent : baseEnd_1371582 < baseStart_1371582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371595 : List Nat := [1, 1, 1, 1, 3, 3, 13]
def baseStart_1371595 : Nat := 118140960795 + 1371595 * 2 ^ 59
def prefixEnd_1371595 : Nat := 4983230072969 + 3 ^ 40 * 1371595 * 2
def baseEnd_1371595 : Nat := 8694907386465016814255

theorem tailTrace_1371595 : CollatzResearch.WordTrace tailWord_1371595 prefixEnd_1371595 8694907386465016814255 := by
  unfold tailWord_1371595
  simp only [CollatzResearch.WordTrace]
  refine ⟨50026179465953039621532239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33350786310635359747688159 50026179465953039621532239)
  ·
    refine ⟨75039269198929559432298359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50026179465953039621532239 75039269198929559432298359)
    ·
      refine ⟨112558903798394339148447539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75039269198929559432298359 112558903798394339148447539)
      ·
        refine ⟨168838355697591508722671309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112558903798394339148447539 168838355697591508722671309)
        ·
          refine ⟨63314383386596815771001741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168838355697591508722671309 63314383386596815771001741)
          ·
            refine ⟨23742893769973805914125653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63314383386596815771001741 23742893769973805914125653)
            ·
              refine ⟨8694907386465016814255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 23742893769973805914125653 8694907386465016814255)
              ·
                rfl

theorem cell23_1371595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 13].length) (baseStart_1371595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371595 prefixEnd_1371595 := by exact prefixLift 1371595
  have htrace : WordTrace (prefixWord ++ tailWord_1371595) baseStart_1371595 baseEnd_1371595 := by
    simpa [prefixWord, tailWord_1371595, baseEnd_1371595] using wordTrace_append hprefix tailTrace_1371595
  have hstable : (prefixWord ++ tailWord_1371595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371595).length < 2 ^ (prefixWord ++ tailWord_1371595).sum := by decide
  have hdescent : baseEnd_1371595 < baseStart_1371595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371626 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1371626 : Nat := 118140960795 + 1371626 * 2 ^ 59
def prefixEnd_1371626 : Nat := 4983230072969 + 3 ^ 40 * 1371626 * 2
def baseEnd_1371626 : Nat := 704303416203955740667013

theorem tailTrace_1371626 : CollatzResearch.WordTrace tailWord_1371626 prefixEnd_1371626 704303416203955740667013 := by
  unfold tailWord_1371626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506827532210182978977683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33351540085893821277273821 12506827532210182978977683)
  ·
    refine ⟨18760241298315274468466525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12506827532210182978977683 18760241298315274468466525)
    ·
      refine ⟨7035090486868227925674947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18760241298315274468466525 7035090486868227925674947)
      ·
        refine ⟨10552635730302341888512421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035090486868227925674947 10552635730302341888512421)
        ·
          refine ⟨1978619199431689104096079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10552635730302341888512421 1978619199431689104096079)
          ·
            refine ⟨2967928799147533656144119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978619199431689104096079 2967928799147533656144119)
            ·
              refine ⟨4451893198721300484216179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967928799147533656144119 4451893198721300484216179)
              ·
                refine ⟨6677839798081950726324269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4451893198721300484216179 6677839798081950726324269)
                ·
                  refine ⟨2504189924280731522371601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6677839798081950726324269 2504189924280731522371601)
                  ·
                    refine ⟨1878142443210548641778701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504189924280731522371601 1878142443210548641778701)
                    ·
                      refine ⟨704303416203955740667013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878142443210548641778701 704303416203955740667013)
                      ·
                        rfl

theorem cell23_1371626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1371626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371626 prefixEnd_1371626 := by exact prefixLift 1371626
  have htrace : WordTrace (prefixWord ++ tailWord_1371626) baseStart_1371626 baseEnd_1371626 := by
    simpa [prefixWord, tailWord_1371626, baseEnd_1371626] using wordTrace_append hprefix tailTrace_1371626
  have hstable : (prefixWord ++ tailWord_1371626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371626).length < 2 ^ (prefixWord ++ tailWord_1371626).sum := by decide
  have hdescent : baseEnd_1371626 < baseStart_1371626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371639 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_1371639 : Nat := 118140960795 + 1371639 * 2 ^ 59
def prefixEnd_1371639 : Nat := 4983230072969 + 3 ^ 40 * 1371639 * 2
def baseEnd_1371639 : Nat := 704310091452464189804453

theorem tailTrace_1371639 : CollatzResearch.WordTrace tailWord_1371639 prefixEnd_1371639 704310091452464189804453 := by
  unfold tailWord_1371639
  simp only [CollatzResearch.WordTrace]
  refine ⟨50027784277793635136133971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33351856185195756757422647 50027784277793635136133971)
  ·
    refine ⟨75041676416690452704200957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50027784277793635136133971 75041676416690452704200957)
    ·
      refine ⟨28140628656258919764075359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75041676416690452704200957 28140628656258919764075359)
      ·
        refine ⟨42210942984388379646113039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28140628656258919764075359 42210942984388379646113039)
        ·
          refine ⟨63316414476582569469169559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42210942984388379646113039 63316414476582569469169559)
          ·
            refine ⟨94974621714873854203754339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63316414476582569469169559 94974621714873854203754339)
            ·
              refine ⟨142461932572310781305631509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94974621714873854203754339 142461932572310781305631509)
              ·
                refine ⟨6677903089327067873701477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142461932572310781305631509 6677903089327067873701477)
                ·
                  refine ⟨1252106829248825226319027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6677903089327067873701477 1252106829248825226319027)
                  ·
                    refine ⟨1878160243873237839478541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252106829248825226319027 1878160243873237839478541)
                    ·
                      refine ⟨704310091452464189804453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878160243873237839478541 704310091452464189804453)
                      ·
                        rfl

theorem cell23_1371639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_1371639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371639 prefixEnd_1371639 := by exact prefixLift 1371639
  have htrace : WordTrace (prefixWord ++ tailWord_1371639) baseStart_1371639 baseEnd_1371639 := by
    simpa [prefixWord, tailWord_1371639, baseEnd_1371639] using wordTrace_append hprefix tailTrace_1371639
  have hstable : (prefixWord ++ tailWord_1371639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371639).length < 2 ^ (prefixWord ++ tailWord_1371639).sum := by decide
  have hdescent : baseEnd_1371639 < baseStart_1371639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371646 : List Nat := [4, 2, 2, 3, 2, 10]
def baseStart_1371646 : Nat := 118140960795 + 1371646 * 2 ^ 59
def prefixEnd_1371646 : Nat := 4983230072969 + 3 ^ 40 * 1371646 * 2
def baseEnd_1371646 : Nat := 2898410229699776388547

theorem tailTrace_1371646 : CollatzResearch.WordTrace tailWord_1371646 prefixEnd_1371646 2898410229699776388547 := by
  unfold tailWord_1371646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253504948596034416454849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33352026392512183554425861 6253504948596034416454849)
  ·
    refine ⟨4690128711447025812341137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6253504948596034416454849 4690128711447025812341137)
    ·
      refine ⟨3517596533585269359255853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690128711447025812341137 3517596533585269359255853)
      ·
        refine ⟨1319098700094476009720945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3517596533585269359255853 1319098700094476009720945)
        ·
          refine ⟨989324025070857007290709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319098700094476009720945 989324025070857007290709)
          ·
            refine ⟨2898410229699776388547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 989324025070857007290709 2898410229699776388547)
            ·
              rfl

theorem cell23_1371646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 10].length) (baseStart_1371646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371646 prefixEnd_1371646 := by exact prefixLift 1371646
  have htrace : WordTrace (prefixWord ++ tailWord_1371646) baseStart_1371646 baseEnd_1371646 := by
    simpa [prefixWord, tailWord_1371646, baseEnd_1371646] using wordTrace_append hprefix tailTrace_1371646
  have hstable : (prefixWord ++ tailWord_1371646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371646).length < 2 ^ (prefixWord ++ tailWord_1371646).sum := by decide
  have hdescent : baseEnd_1371646 < baseStart_1371646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371656 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_1371656 : Nat := 118140960795 + 1371656 * 2 ^ 59
def prefixEnd_1371656 : Nat := 4983230072969 + 3 ^ 40 * 1371656 * 2
def baseEnd_1371656 : Nat := 704318820623590623291875

theorem tailTrace_1371656 : CollatzResearch.WordTrace tailWord_1371656 prefixEnd_1371656 704318820623590623291875 := by
  unfold tailWord_1371656
  simp only [CollatzResearch.WordTrace]
  refine ⟨25014202159366023519751411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33352269545821364693001881 25014202159366023519751411)
  ·
    refine ⟨37521303239049035279627117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25014202159366023519751411 37521303239049035279627117)
    ·
      refine ⟨14070488714643388229860169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37521303239049035279627117 14070488714643388229860169)
      ·
        refine ⟨10552866535982541172395127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14070488714643388229860169 10552866535982541172395127)
        ·
          refine ⟨15829299803973811758592691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10552866535982541172395127 15829299803973811758592691)
          ·
            refine ⟨23743949705960717637889037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15829299803973811758592691 23743949705960717637889037)
            ·
              refine ⟨8903981139735269114208389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23743949705960717637889037 8903981139735269114208389)
              ·
                refine ⟨1669496463700362958914073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8903981139735269114208389 1669496463700362958914073)
                ·
                  refine ⟨1252122347775272219185555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669496463700362958914073 1252122347775272219185555)
                  ·
                    refine ⟨1878183521662908328778333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252122347775272219185555 1878183521662908328778333)
                    ·
                      refine ⟨704318820623590623291875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878183521662908328778333 704318820623590623291875)
                      ·
                        rfl

theorem cell23_1371656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_1371656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371656 prefixEnd_1371656 := by exact prefixLift 1371656
  have htrace : WordTrace (prefixWord ++ tailWord_1371656) baseStart_1371656 baseEnd_1371656 := by
    simpa [prefixWord, tailWord_1371656, baseEnd_1371656] using wordTrace_append hprefix tailTrace_1371656
  have hstable : (prefixWord ++ tailWord_1371656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371656).length < 2 ^ (prefixWord ++ tailWord_1371656).sum := by decide
  have hdescent : baseEnd_1371656 < baseStart_1371656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371696 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2]
def baseStart_1371696 : Nat := 118140960795 + 1371696 * 2 ^ 59
def prefixEnd_1371696 : Nat := 4983230072969 + 3 ^ 40 * 1371696 * 2
def baseEnd_1371696 : Nat := 704339359849770466791691

theorem tailTrace_1371696 : CollatzResearch.WordTrace tailWord_1371696 prefixEnd_1371696 704339359849770466791691 := by
  unfold tailWord_1371696
  simp only [CollatzResearch.WordTrace]
  refine ⟨25014931619293566935479471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33353242159058089247305961 25014931619293566935479471)
  ·
    refine ⟨37522397428940350403219207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25014931619293566935479471 37522397428940350403219207)
    ·
      refine ⟨56283596143410525604828811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37522397428940350403219207 56283596143410525604828811)
      ·
        refine ⟨84425394215115788407243217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56283596143410525604828811 84425394215115788407243217)
        ·
          refine ⟨63319045661336841305432413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84425394215115788407243217 63319045661336841305432413)
          ·
            refine ⟨23744642123001315489537155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63319045661336841305432413 23744642123001315489537155)
            ·
              refine ⟨35616963184501973234305733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23744642123001315489537155 35616963184501973234305733)
              ·
                refine ⟨6678180597094119981432325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35616963184501973234305733 6678180597094119981432325)
                ·
                  refine ⟨1252158861955147496518561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6678180597094119981432325 1252158861955147496518561)
                  ·
                    refine ⟨939119146466360622388921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1252158861955147496518561 939119146466360622388921)
                    ·
                      refine ⟨704339359849770466791691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939119146466360622388921 704339359849770466791691)
                      ·
                        rfl

theorem cell23_1371696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 4, 2, 2].length) (baseStart_1371696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371696 prefixEnd_1371696 := by exact prefixLift 1371696
  have htrace : WordTrace (prefixWord ++ tailWord_1371696) baseStart_1371696 baseEnd_1371696 := by
    simpa [prefixWord, tailWord_1371696, baseEnd_1371696] using wordTrace_append hprefix tailTrace_1371696
  have hstable : (prefixWord ++ tailWord_1371696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371696).length < 2 ^ (prefixWord ++ tailWord_1371696).sum := by decide
  have hdescent : baseEnd_1371696 < baseStart_1371696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371713 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1371713 : Nat := 118140960795 + 1371713 * 2 ^ 59
def prefixEnd_1371713 : Nat := 4983230072969 + 3 ^ 40 * 1371713 * 2
def baseEnd_1371713 : Nat := 704348089020896900279113

theorem tailTrace_1371713 : CollatzResearch.WordTrace tailWord_1371713 prefixEnd_1371713 704348089020896900279113 := by
  unfold tailWord_1371713
  simp only [CollatzResearch.WordTrace]
  refine ⟨50030483279525545774327793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33353655519683697182885195 50030483279525545774327793)
  ·
    refine ⟨37522862459644159330745845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50030483279525545774327793 37522862459644159330745845)
    ·
      refine ⟨3517768355591639937257423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37522862459644159330745845 3517768355591639937257423)
      ·
        refine ⟨5276652533387459905886135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517768355591639937257423 5276652533387459905886135)
        ·
          refine ⟨7914978800081189858829203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276652533387459905886135 7914978800081189858829203)
          ·
            refine ⟨11872468200121784788243805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914978800081189858829203 11872468200121784788243805)
            ·
              refine ⟨4452175575045669295591427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11872468200121784788243805 4452175575045669295591427)
              ·
                refine ⟨6678263362568503943387141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452175575045669295591427 6678263362568503943387141)
                ·
                  refine ⟨1252174380481594489385089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6678263362568503943387141 1252174380481594489385089)
                  ·
                    refine ⟨939130785361195867038817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1252174380481594489385089 939130785361195867038817)
                    ·
                      refine ⟨704348089020896900279113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939130785361195867038817 704348089020896900279113)
                      ·
                        rfl

theorem cell23_1371713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1371713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371713 prefixEnd_1371713 := by exact prefixLift 1371713
  have htrace : WordTrace (prefixWord ++ tailWord_1371713) baseStart_1371713 baseEnd_1371713 := by
    simpa [prefixWord, tailWord_1371713, baseEnd_1371713] using wordTrace_append hprefix tailTrace_1371713
  have hstable : (prefixWord ++ tailWord_1371713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371713).length < 2 ^ (prefixWord ++ tailWord_1371713).sum := by decide
  have hdescent : baseEnd_1371713 < baseStart_1371713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371729 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_1371729 : Nat := 118140960795 + 1371729 * 2 ^ 59
def prefixEnd_1371729 : Nat := 4983230072969 + 3 ^ 40 * 1371729 * 2
def baseEnd_1371729 : Nat := 704356304711368837679039

theorem tailTrace_1371729 : CollatzResearch.WordTrace tailWord_1371729 prefixEnd_1371729 704356304711368837679039 := by
  unfold tailWord_1371729
  simp only [CollatzResearch.WordTrace]
  refine ⟨50031066847467580506910241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33354044564978387004606827 50031066847467580506910241)
  ·
    refine ⟨37523300135600685380182681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50031066847467580506910241 37523300135600685380182681)
    ·
      refine ⟨28142475101700514035137011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37523300135600685380182681 28142475101700514035137011)
      ·
        refine ⟨42213712652550771052705517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28142475101700514035137011 42213712652550771052705517)
        ·
          refine ⟨15830142244706539144764569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42213712652550771052705517 15830142244706539144764569)
          ·
            refine ⟨11872606683529904358573427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15830142244706539144764569 11872606683529904358573427)
            ·
              refine ⟨17808910025294856537860141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11872606683529904358573427 17808910025294856537860141)
              ·
                refine ⟨6678341259485571201697553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17808910025294856537860141 6678341259485571201697553)
                ·
                  refine ⟨5008755944614178401273165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6678341259485571201697553 5008755944614178401273165)
                  ·
                    refine ⟨1878283479230316900477437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5008755944614178401273165 1878283479230316900477437)
                    ·
                      refine ⟨704356304711368837679039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878283479230316900477437 704356304711368837679039)
                      ·
                        rfl

theorem cell23_1371729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_1371729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371729 prefixEnd_1371729 := by exact prefixLift 1371729
  have htrace : WordTrace (prefixWord ++ tailWord_1371729) baseStart_1371729 baseEnd_1371729 := by
    simpa [prefixWord, tailWord_1371729, baseEnd_1371729] using wordTrace_append hprefix tailTrace_1371729
  have hstable : (prefixWord ++ tailWord_1371729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371729).length < 2 ^ (prefixWord ++ tailWord_1371729).sum := by decide
  have hdescent : baseEnd_1371729 < baseStart_1371729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371734 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_1371734 : Nat := 118140960795 + 1371734 * 2 ^ 59
def prefixEnd_1371734 : Nat := 4983230072969 + 3 ^ 40 * 1371734 * 2
def baseEnd_1371734 : Nat := 704358872114641318116517

theorem tailTrace_1371734 : CollatzResearch.WordTrace tailWord_1371734 prefixEnd_1371734 704358872114641318116517 := by
  unfold tailWord_1371734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126953075778091647552641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33354166141632977573894837 3126953075778091647552641)
  ·
    refine ⟨2345214806833568735664481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3126953075778091647552641 2345214806833568735664481)
    ·
      refine ⟨1758911105125176551748361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2345214806833568735664481 1758911105125176551748361)
      ·
        refine ⟨1319183328843882413811271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1758911105125176551748361 1319183328843882413811271)
        ·
          refine ⟨1978774993265823620716907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319183328843882413811271 1978774993265823620716907)
          ·
            refine ⟨2968162489898735431075361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978774993265823620716907 2968162489898735431075361)
            ·
              refine ⟨2226121867424051573306521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968162489898735431075361 2226121867424051573306521)
              ·
                refine ⟨1669591400568038679979891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226121867424051573306521 1669591400568038679979891)
                ·
                  refine ⟨2504387100852058019969837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669591400568038679979891 2504387100852058019969837)
                  ·
                    refine ⟨939145162819521757488689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504387100852058019969837 939145162819521757488689)
                    ·
                      refine ⟨704358872114641318116517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 939145162819521757488689 704358872114641318116517)
                      ·
                        rfl

theorem cell23_1371734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_1371734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371734 prefixEnd_1371734 := by exact prefixLift 1371734
  have htrace : WordTrace (prefixWord ++ tailWord_1371734) baseStart_1371734 baseEnd_1371734 := by
    simpa [prefixWord, tailWord_1371734, baseEnd_1371734] using wordTrace_append hprefix tailTrace_1371734
  have hstable : (prefixWord ++ tailWord_1371734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371734).length < 2 ^ (prefixWord ++ tailWord_1371734).sum := by decide
  have hdescent : baseEnd_1371734 < baseStart_1371734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371749 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1371749 : Nat := 118140960795 + 1371749 * 2 ^ 59
def prefixEnd_1371749 : Nat := 4983230072969 + 3 ^ 40 * 1371749 * 2
def baseEnd_1371749 : Nat := 234788858108152919809649

theorem tailTrace_1371749 : CollatzResearch.WordTrace tailWord_1371749 prefixEnd_1371749 234788858108152919809649 := by
  unfold tailWord_1371749
  simp only [CollatzResearch.WordTrace]
  refine ⟨50031796307395123922638301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33354530871596749281758867 50031796307395123922638301)
  ·
    refine ⟨18761923615273171470989363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50031796307395123922638301 18761923615273171470989363)
    ·
      refine ⟨28142885422909757206484045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18761923615273171470989363 28142885422909757206484045)
      ·
        refine ⟨10553582033591158952431517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28142885422909757206484045 10553582033591158952431517)
        ·
          refine ⟨3957593262596684607161819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10553582033591158952431517 3957593262596684607161819)
          ·
            refine ⟨5936389893895026910742729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957593262596684607161819 5936389893895026910742729)
            ·
              refine ⟨4452292420421270183057047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5936389893895026910742729 4452292420421270183057047)
              ·
                refine ⟨6678438630631905274585571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452292420421270183057047 6678438630631905274585571)
                ·
                  refine ⟨10017657945947857911878357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6678438630631905274585571 10017657945947857911878357)
                  ·
                    refine ⟨234788858108152919809649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10017657945947857911878357 234788858108152919809649)
                    ·
                      rfl

theorem cell23_1371749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1371749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371749 prefixEnd_1371749 := by exact prefixLift 1371749
  have htrace : WordTrace (prefixWord ++ tailWord_1371749) baseStart_1371749 baseEnd_1371749 := by
    simpa [prefixWord, tailWord_1371749, baseEnd_1371749] using wordTrace_append hprefix tailTrace_1371749
  have hstable : (prefixWord ++ tailWord_1371749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371749).length < 2 ^ (prefixWord ++ tailWord_1371749).sum := by decide
  have hdescent : baseEnd_1371749 < baseStart_1371749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371766 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1371766 : Nat := 118140960795 + 1371766 * 2 ^ 59
def prefixEnd_1371766 : Nat := 4983230072969 + 3 ^ 40 * 1371766 * 2
def baseEnd_1371766 : Nat := 234791767831861730972123

theorem tailTrace_1371766 : CollatzResearch.WordTrace tailWord_1371766 prefixEnd_1371766 234791767831861730972123 := by
  unfold tailWord_1371766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127026021770845989125447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33354944232222357217338101 3127026021770845989125447)
  ·
    refine ⟨4690539032656268983688171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3127026021770845989125447 4690539032656268983688171)
    ·
      refine ⟨7035808548984403475532257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690539032656268983688171 7035808548984403475532257)
      ·
        refine ⟨5276856411738302606649193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7035808548984403475532257 5276856411738302606649193)
        ·
          refine ⟨3957642308803726954986895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5276856411738302606649193 3957642308803726954986895)
          ·
            refine ⟨5936463463205590432480343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957642308803726954986895 5936463463205590432480343)
            ·
              refine ⟨8904695194808385648720515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936463463205590432480343 8904695194808385648720515)
              ·
                refine ⟨13357042792212578473080773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8904695194808385648720515 13357042792212578473080773)
                ·
                  refine ⟨2504445523539858463702645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13357042792212578473080773 2504445523539858463702645)
                  ·
                    refine ⟨234791767831861730972123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2504445523539858463702645 234791767831861730972123)
                    ·
                      rfl

theorem cell23_1371766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1371766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371766 prefixEnd_1371766 := by exact prefixLift 1371766
  have htrace : WordTrace (prefixWord ++ tailWord_1371766) baseStart_1371766 baseEnd_1371766 := by
    simpa [prefixWord, tailWord_1371766, baseEnd_1371766] using wordTrace_append hprefix tailTrace_1371766
  have hstable : (prefixWord ++ tailWord_1371766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371766).length < 2 ^ (prefixWord ++ tailWord_1371766).sum := by decide
  have hdescent : baseEnd_1371766 < baseStart_1371766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371839 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 5, 5]
def baseStart_1371839 : Nat := 118140960795 + 1371839 * 2 ^ 59
def prefixEnd_1371839 : Nat := 4983230072969 + 3 ^ 40 * 1371839 * 2
def baseEnd_1371839 : Nat := 234804262527787802434511

theorem tailTrace_1371839 : CollatzResearch.WordTrace tailWord_1371839 prefixEnd_1371839 234804262527787802434511 := by
  unfold tailWord_1371839
  simp only [CollatzResearch.WordTrace]
  refine ⟨50035078877069069293414571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33356719251379379528943047 50035078877069069293414571)
  ·
    refine ⟨75052618315603603940121857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50035078877069069293414571 75052618315603603940121857)
    ·
      refine ⟨56289463736702702955091393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75052618315603603940121857 56289463736702702955091393)
      ·
        refine ⟨42217097802527027216318545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56289463736702702955091393 42217097802527027216318545)
        ·
          refine ⟨31662823351895270412238909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42217097802527027216318545 31662823351895270412238909)
          ·
            refine ⟨11873558756960726404589591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31662823351895270412238909 11873558756960726404589591)
            ·
              refine ⟨17810338135441089606884387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11873558756960726404589591 17810338135441089606884387)
              ·
                refine ⟨26715507203161634410326581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17810338135441089606884387 26715507203161634410326581)
                ·
                  refine ⟨2504578800296403225968117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26715507203161634410326581 2504578800296403225968117)
                  ·
                    refine ⟨234804262527787802434511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2504578800296403225968117 234804262527787802434511)
                    ·
                      rfl

theorem cell23_1371839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_1371839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371839 prefixEnd_1371839 := by exact prefixLift 1371839
  have htrace : WordTrace (prefixWord ++ tailWord_1371839) baseStart_1371839 baseEnd_1371839 := by
    simpa [prefixWord, tailWord_1371839, baseEnd_1371839] using wordTrace_append hprefix tailTrace_1371839
  have hstable : (prefixWord ++ tailWord_1371839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371839).length < 2 ^ (prefixWord ++ tailWord_1371839).sum := by decide
  have hdescent : baseEnd_1371839 < baseStart_1371839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371873 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1371873 : Nat := 118140960795 + 1371873 * 2 ^ 59
def prefixEnd_1371873 : Nat := 4983230072969 + 3 ^ 40 * 1371873 * 2
def baseEnd_1371873 : Nat := 234810081975205424759459

theorem tailTrace_1371873 : CollatzResearch.WordTrace tailWord_1371873 prefixEnd_1371873 234810081975205424759459 := by
  unfold tailWord_1371873
  simp only [CollatzResearch.WordTrace]
  refine ⟨50036318958945893100152273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33357545972630595400101515 50036318958945893100152273)
  ·
    refine ⟨37527239219209419825114205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50036318958945893100152273 37527239219209419825114205)
    ·
      refine ⟨14072714707203532434417827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37527239219209419825114205 14072714707203532434417827)
      ·
        refine ⟨21109072060805298651626741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14072714707203532434417827 21109072060805298651626741)
        ·
          refine ⟨1978975505700496748590007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21109072060805298651626741 1978975505700496748590007)
          ·
            refine ⟨2968463258550745122885011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978975505700496748590007 2968463258550745122885011)
            ·
              refine ⟨4452694887826117684327517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968463258550745122885011 4452694887826117684327517)
              ·
                refine ⟨1669760582934794131622819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4452694887826117684327517 1669760582934794131622819)
                ·
                  refine ⟨2504640874402191197434229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669760582934794131622819 2504640874402191197434229)
                  ·
                    refine ⟨234810081975205424759459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2504640874402191197434229 234810081975205424759459)
                    ·
                      rfl

theorem cell23_1371873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1371873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371873 prefixEnd_1371873 := by exact prefixLift 1371873
  have htrace : WordTrace (prefixWord ++ tailWord_1371873) baseStart_1371873 baseEnd_1371873 := by
    simpa [prefixWord, tailWord_1371873, baseEnd_1371873] using wordTrace_append hprefix tailTrace_1371873
  have hstable : (prefixWord ++ tailWord_1371873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371873).length < 2 ^ (prefixWord ++ tailWord_1371873).sum := by decide
  have hdescent : baseEnd_1371873 < baseStart_1371873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1371896 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_1371896 : Nat := 118140960795 + 1371896 * 2 ^ 59
def prefixEnd_1371896 : Nat := 4983230072969 + 3 ^ 40 * 1371896 * 2
def baseEnd_1371896 : Nat := 704442055980669684290771

theorem tailTrace_1371896 : CollatzResearch.WordTrace tailWord_1371896 prefixEnd_1371896 704442055980669684290771 := by
  unfold tailWord_1371896
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018578918931284014119771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33358105225241712018826361 25018578918931284014119771)
  ·
    refine ⟨37527868378396926021179657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25018578918931284014119771 37527868378396926021179657)
    ·
      refine ⟨28145901283797694515884743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37527868378396926021179657 28145901283797694515884743)
      ·
        refine ⟨42218851925696541773827115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28145901283797694515884743 42218851925696541773827115)
        ·
          refine ⟨63328277888544812660740673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42218851925696541773827115 63328277888544812660740673)
          ·
            refine ⟨47496208416408609495555505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63328277888544812660740673 47496208416408609495555505)
            ·
              refine ⟨35622156312306457121666629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47496208416408609495555505 35622156312306457121666629)
              ·
                refine ⟨6679154308557460710312493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35622156312306457121666629 6679154308557460710312493)
                ·
                  refine ⟨2504682865709047766367185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6679154308557460710312493 2504682865709047766367185)
                  ·
                    refine ⟨1878512149281785824775389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504682865709047766367185 1878512149281785824775389)
                    ·
                      refine ⟨704442055980669684290771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1878512149281785824775389 704442055980669684290771)
                      ·
                        rfl

theorem cell23_1371896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_1371896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1371896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1371896 prefixEnd_1371896 := by exact prefixLift 1371896
  have htrace : WordTrace (prefixWord ++ tailWord_1371896) baseStart_1371896 baseEnd_1371896 := by
    simpa [prefixWord, tailWord_1371896, baseEnd_1371896] using wordTrace_append hprefix tailTrace_1371896
  have hstable : (prefixWord ++ tailWord_1371896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1371896).length < 2 ^ (prefixWord ++ tailWord_1371896).sum := by decide
  have hdescent : baseEnd_1371896 < baseStart_1371896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1371896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
