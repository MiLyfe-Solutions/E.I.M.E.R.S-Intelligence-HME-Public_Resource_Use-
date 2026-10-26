import V185TrunkScan23Chunk1271

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7536003 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5]
def baseStart_7536003 : Nat := 118140960795 + 7536003 * 2 ^ 59
def prefixEnd_7536003 : Nat := 4983230072969 + 3 ^ 40 * 7536003 * 2
def baseEnd_7536003 : Nat := 3869591752724584087305059

theorem tailTrace_7536003 : CollatzResearch.WordTrace tailWord_7536003 prefixEnd_7536003 3869591752724584087305059 := by
  unfold tailWord_7536003
  simp only [CollatzResearch.WordTrace]
  refine ⟨274860610117355652690476663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183240406744903768460317775 274860610117355652690476663)
  ·
    refine ⟨412290915176033479035714995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274860610117355652690476663 412290915176033479035714995)
    ·
      refine ⟨618436372764050218553572493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412290915176033479035714995 618436372764050218553572493)
      ·
        refine ⟨231913639786518831957589685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618436372764050218553572493 231913639786518831957589685)
        ·
          refine ⟨21741903729986140496024033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231913639786518831957589685 21741903729986140496024033)
          ·
            refine ⟨16306427797489605372018025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21741903729986140496024033 16306427797489605372018025)
            ·
              refine ⟨12229820848117204029013519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306427797489605372018025 12229820848117204029013519)
              ·
                refine ⟨18344731272175806043520279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229820848117204029013519 18344731272175806043520279)
                ·
                  refine ⟨27517096908263709065280419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18344731272175806043520279 27517096908263709065280419)
                  ·
                    refine ⟨41275645362395563597920629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27517096908263709065280419 41275645362395563597920629)
                    ·
                      refine ⟨3869591752724584087305059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41275645362395563597920629 3869591752724584087305059)
                      ·
                        rfl

theorem cell23_7536003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_7536003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536003 prefixEnd_7536003 := by exact prefixLift 7536003
  have htrace : WordTrace (prefixWord ++ tailWord_7536003) baseStart_7536003 baseEnd_7536003 := by
    simpa [prefixWord, tailWord_7536003, baseEnd_7536003] using wordTrace_append hprefix tailTrace_7536003
  have hstable : (prefixWord ++ tailWord_7536003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536003).length < 2 ^ (prefixWord ++ tailWord_7536003).sum := by decide
  have hdescent : baseEnd_7536003 < baseStart_7536003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536026 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7536026 : Nat := 118140960795 + 7536026 * 2 ^ 59
def prefixEnd_7536026 : Nat := 4983230072969 + 3 ^ 40 * 7536026 * 2
def baseEnd_7536026 : Nat := 3869603562779637497317453

theorem tailTrace_7536026 : CollatzResearch.WordTrace tailWord_7536026 prefixEnd_7536026 3869603562779637497317453 := by
  unfold tailWord_7536026
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715362249068081904640983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183240965997514885079042621 68715362249068081904640983)
  ·
    refine ⟨103073043373602122856961475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68715362249068081904640983 103073043373602122856961475)
    ·
      refine ⟨154609565060403184285442213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103073043373602122856961475 154609565060403184285442213)
      ·
        refine ⟨28989293448825597053520415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154609565060403184285442213 28989293448825597053520415)
        ·
          refine ⟨43483940173238395580280623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28989293448825597053520415 43483940173238395580280623)
          ·
            refine ⟨65225910259857593370420935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43483940173238395580280623 65225910259857593370420935)
            ·
              refine ⟨97838865389786390055631403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65225910259857593370420935 97838865389786390055631403)
              ·
                refine ⟨146758298084679585083447105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97838865389786390055631403 146758298084679585083447105)
                ·
                  refine ⟨110068723563509688812585329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146758298084679585083447105 110068723563509688812585329)
                  ·
                    refine ⟨82551542672632266609438997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110068723563509688812585329 82551542672632266609438997)
                    ·
                      refine ⟨3869603562779637497317453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82551542672632266609438997 3869603562779637497317453)
                      ·
                        rfl

theorem cell23_7536026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7536026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536026 prefixEnd_7536026 := by exact prefixLift 7536026
  have htrace : WordTrace (prefixWord ++ tailWord_7536026) baseStart_7536026 baseEnd_7536026 := by
    simpa [prefixWord, tailWord_7536026, baseEnd_7536026] using wordTrace_append hprefix tailTrace_7536026
  have hstable : (prefixWord ++ tailWord_7536026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536026).length < 2 ^ (prefixWord ++ tailWord_7536026).sum := by decide
  have hdescent : baseEnd_7536026 < baseStart_7536026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536068 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7536068 : Nat := 118140960795 + 7536068 * 2 ^ 59
def prefixEnd_7536068 : Nat := 4983230072969 + 3 ^ 40 * 7536068 * 2
def baseEnd_7536068 : Nat := 3869625128967126332992261

theorem tailTrace_7536068 : CollatzResearch.WordTrace tailWord_7536068 prefixEnd_7536068 3869625128967126332992261 := by
  unfold tailWord_7536068
  simp only [CollatzResearch.WordTrace]
  refine ⟨137431490431060084395796429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183241987241413445861061905 137431490431060084395796429)
  ·
    refine ⟨51536808911647531648423661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137431490431060084395796429 51536808911647531648423661)
    ·
      refine ⟨19326303341867824368158873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51536808911647531648423661 19326303341867824368158873)
      ·
        refine ⟨14494727506400868276119155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19326303341867824368158873 14494727506400868276119155)
        ·
          refine ⟨21742091259601302414178733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14494727506400868276119155 21742091259601302414178733)
          ·
            refine ⟨8153284222350488405317025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21742091259601302414178733 8153284222350488405317025)
            ·
              refine ⟨6114963166762866303987769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153284222350488405317025 6114963166762866303987769)
              ·
                refine ⟨4586222375072149727990827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6114963166762866303987769 4586222375072149727990827)
                ·
                  refine ⟨6879333562608224591986241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586222375072149727990827 6879333562608224591986241)
                  ·
                    refine ⟨5159500171956168443989681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879333562608224591986241 5159500171956168443989681)
                    ·
                      refine ⟨3869625128967126332992261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159500171956168443989681 3869625128967126332992261)
                      ·
                        rfl

theorem cell23_7536068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7536068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536068 prefixEnd_7536068 := by exact prefixLift 7536068
  have htrace : WordTrace (prefixWord ++ tailWord_7536068) baseStart_7536068 baseEnd_7536068 := by
    simpa [prefixWord, tailWord_7536068, baseEnd_7536068] using wordTrace_append hprefix tailTrace_7536068
  have hstable : (prefixWord ++ tailWord_7536068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536068).length < 2 ^ (prefixWord ++ tailWord_7536068).sum := by decide
  have hdescent : baseEnd_7536068 < baseStart_7536068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536073 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 5, 4, 2]
def baseStart_7536073 : Nat := 118140960795 + 7536073 * 2 ^ 59
def prefixEnd_7536073 : Nat := 4983230072969 + 3 ^ 40 * 7536073 * 2
def baseEnd_7536073 : Nat := 3869627696370398813429737

theorem tailTrace_7536073 : CollatzResearch.WordTrace tailWord_7536073 prefixEnd_7536073 3869627696370398813429737 := by
  unfold tailWord_7536073
  simp only [CollatzResearch.WordTrace]
  refine ⟨274863163227102054645524873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183242108818068036430349915 274863163227102054645524873)
  ·
    refine ⟨206147372420326540984143655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274863163227102054645524873 206147372420326540984143655)
    ·
      refine ⟨309221058630489811476215483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206147372420326540984143655 309221058630489811476215483)
      ·
        refine ⟨463831587945734717214323225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309221058630489811476215483 463831587945734717214323225)
        ·
          refine ⟨347873690959301037910742419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463831587945734717214323225 347873690959301037910742419)
          ·
            refine ⟨521810536438951556866113629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347873690959301037910742419 521810536438951556866113629)
            ·
              refine ⟨195678951164606833824792611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521810536438951556866113629 195678951164606833824792611)
              ·
                refine ⟨293518426746910250737188917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195678951164606833824792611 293518426746910250737188917)
                ·
                  refine ⟨27517352507522836006611461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293518426746910250737188917 27517352507522836006611461)
                  ·
                    refine ⟨5159503595160531751239649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27517352507522836006611461 5159503595160531751239649)
                    ·
                      refine ⟨3869627696370398813429737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159503595160531751239649 3869627696370398813429737)
                      ·
                        rfl

theorem cell23_7536073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 4, 2].length) (baseStart_7536073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536073 prefixEnd_7536073 := by exact prefixLift 7536073
  have htrace : WordTrace (prefixWord ++ tailWord_7536073) baseStart_7536073 baseEnd_7536073 := by
    simpa [prefixWord, tailWord_7536073, baseEnd_7536073] using wordTrace_append hprefix tailTrace_7536073
  have hstable : (prefixWord ++ tailWord_7536073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536073).length < 2 ^ (prefixWord ++ tailWord_7536073).sum := by decide
  have hdescent : baseEnd_7536073 < baseStart_7536073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536090 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2]
def baseStart_7536090 : Nat := 118140960795 + 7536090 * 2 ^ 59
def prefixEnd_7536090 : Nat := 4983230072969 + 3 ^ 40 * 7536090 * 2
def baseEnd_7536090 : Nat := 3869636425541525246917159

theorem tailTrace_7536090 : CollatzResearch.WordTrace tailWord_7536090 prefixEnd_7536090 3869636425541525246917159 := by
  unfold tailWord_7536090
  simp only [CollatzResearch.WordTrace]
  refine ⟨68715945817010116637223431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183242522178693644365929149 68715945817010116637223431)
  ·
    refine ⟨103073918725515174955835147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68715945817010116637223431 103073918725515174955835147)
    ·
      refine ⟨154610878088272762433752721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103073918725515174955835147 154610878088272762433752721)
      ·
        refine ⟨115958158566204571825314541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154610878088272762433752721 115958158566204571825314541)
        ·
          refine ⟨43484309462326714434492953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115958158566204571825314541 43484309462326714434492953)
          ·
            refine ⟨32613232096745035825869715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43484309462326714434492953 32613232096745035825869715)
            ·
              refine ⟨48919848145117553738804573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32613232096745035825869715 48919848145117553738804573)
              ·
                refine ⟨18344943054419082652051715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48919848145117553738804573 18344943054419082652051715)
                ·
                  refine ⟨27517414581628623978077573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18344943054419082652051715 27517414581628623978077573)
                  ·
                    refine ⟨5159515234055366995889545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27517414581628623978077573 5159515234055366995889545)
                    ·
                      refine ⟨3869636425541525246917159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159515234055366995889545 3869636425541525246917159)
                      ·
                        rfl

theorem cell23_7536090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_7536090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536090 prefixEnd_7536090 := by exact prefixLift 7536090
  have htrace : WordTrace (prefixWord ++ tailWord_7536090) baseStart_7536090 baseEnd_7536090 := by
    simpa [prefixWord, tailWord_7536090, baseEnd_7536090] using wordTrace_append hprefix tailTrace_7536090
  have hstable : (prefixWord ++ tailWord_7536090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536090).length < 2 ^ (prefixWord ++ tailWord_7536090).sum := by decide
  have hdescent : baseEnd_7536090 < baseStart_7536090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536130 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_7536130 : Nat := 118140960795 + 7536130 * 2 ^ 59
def prefixEnd_7536130 : Nat := 4983230072969 + 3 ^ 40 * 7536130 * 2
def baseEnd_7536130 : Nat := 429961884974189454490775

theorem tailTrace_7536130 : CollatzResearch.WordTrace tailWord_7536130 prefixEnd_7536130 429961884974189454490775 := by
  unfold tailWord_7536130
  simp only [CollatzResearch.WordTrace]
  refine ⟨68716310546973888345087461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183243494791930368920233229 68716310546973888345087461)
  ·
    refine ⟨12884308227557604064703899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68716310546973888345087461 12884308227557604064703899)
    ·
      refine ⟨19326462341336406097055849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12884308227557604064703899 19326462341336406097055849)
      ·
        refine ⟨14494846756002304572791887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19326462341336406097055849 14494846756002304572791887)
        ·
          refine ⟨21742270134003456859187831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14494846756002304572791887 21742270134003456859187831)
          ·
            refine ⟨32613405201005185288781747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21742270134003456859187831 32613405201005185288781747)
            ·
              refine ⟨48920107801507777933172621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32613405201005185288781747 48920107801507777933172621)
              ·
                refine ⟨18345040425565416724939733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48920107801507777933172621 18345040425565416724939733)
                ·
                  refine ⟨429961884974189454490775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18345040425565416724939733 429961884974189454490775)
                  ·
                    rfl

theorem cell23_7536130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_7536130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536130 prefixEnd_7536130 := by exact prefixLift 7536130
  have htrace : WordTrace (prefixWord ++ tailWord_7536130) baseStart_7536130 baseEnd_7536130 := by
    simpa [prefixWord, tailWord_7536130, baseEnd_7536130] using wordTrace_append hprefix tailTrace_7536130
  have hstable : (prefixWord ++ tailWord_7536130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536130).length < 2 ^ (prefixWord ++ tailWord_7536130).sum := by decide
  have hdescent : baseEnd_7536130 < baseStart_7536130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536237 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 6]
def baseStart_7536237 : Nat := 118140960795 + 7536237 * 2 ^ 59
def prefixEnd_7536237 : Nat := 4983230072969 + 3 ^ 40 * 7536237 * 2
def baseEnd_7536237 : Nat := 429967989688637352419887

theorem tailTrace_7536237 : CollatzResearch.WordTrace tailWord_7536237 prefixEnd_7536237 429967989688637352419887 := by
  unfold tailWord_7536237
  simp only [CollatzResearch.WordTrace]
  refine ⟨274869144798507910654494965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183246096532338607102996643 274869144798507910654494965)
  ·
    refine ⟨25768982324860116623858903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274869144798507910654494965 25768982324860116623858903)
    ·
      refine ⟨38653473487290174935788355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768982324860116623858903 38653473487290174935788355)
      ·
        refine ⟨57980210230935262403682533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38653473487290174935788355 57980210230935262403682533)
        ·
          refine ⟨10871289418300361700690475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57980210230935262403682533 10871289418300361700690475)
          ·
            refine ⟨16306934127450542551035713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871289418300361700690475 16306934127450542551035713)
            ·
              refine ⟨12230200595587906913276785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306934127450542551035713 12230200595587906913276785)
              ·
                refine ⟨9172650446690930184957589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12230200595587906913276785 9172650446690930184957589)
                ·
                  refine ⟨429967989688637352419887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9172650446690930184957589 429967989688637352419887)
                  ·
                    rfl

theorem cell23_7536237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_7536237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536237 prefixEnd_7536237 := by exact prefixLift 7536237
  have htrace : WordTrace (prefixWord ++ tailWord_7536237) baseStart_7536237 baseEnd_7536237 := by
    simpa [prefixWord, tailWord_7536237, baseEnd_7536237] using wordTrace_append hprefix tailTrace_7536237
  have hstable : (prefixWord ++ tailWord_7536237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536237).length < 2 ^ (prefixWord ++ tailWord_7536237).sum := by decide
  have hdescent : baseEnd_7536237 < baseStart_7536237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536273 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_7536273 : Nat := 118140960795 + 7536273 * 2 ^ 59
def prefixEnd_7536273 : Nat := 4983230072969 + 3 ^ 40 * 7536273 * 2
def baseEnd_7536273 : Nat := 3869730392501298030928817

theorem tailTrace_7536273 : CollatzResearch.WordTrace tailWord_7536273 prefixEnd_7536273 3869730392501298030928817 := by
  unfold tailWord_7536273
  simp only [CollatzResearch.WordTrace]
  refine ⟨274870457826377488802805473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183246971884251659201870315 274870457826377488802805473)
  ·
    refine ⟨206152843369783116602104105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274870457826377488802805473 206152843369783116602104105)
    ·
      refine ⟨154614632527337337451578079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206152843369783116602104105 154614632527337337451578079)
      ·
        refine ⟨231921948791006006177367119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154614632527337337451578079 231921948791006006177367119)
        ·
          refine ⟨347882923186509009266050679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231921948791006006177367119 347882923186509009266050679)
          ·
            refine ⟨521824384779763513899076019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347882923186509009266050679 521824384779763513899076019)
            ·
              refine ⟨782736577169645270848614029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521824384779763513899076019 782736577169645270848614029)
              ·
                refine ⟨293526216438616976568230261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 782736577169645270848614029 293526216438616976568230261)
                ·
                  refine ⟨27518082791120341553271587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293526216438616976568230261 27518082791120341553271587)
                  ·
                    refine ⟨41277124186680512329907381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27518082791120341553271587 41277124186680512329907381)
                    ·
                      refine ⟨3869730392501298030928817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41277124186680512329907381 3869730392501298030928817)
                      ·
                        rfl

theorem cell23_7536273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_7536273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536273 prefixEnd_7536273 := by exact prefixLift 7536273
  have htrace : WordTrace (prefixWord ++ tailWord_7536273) baseStart_7536273 baseEnd_7536273 := by
    simpa [prefixWord, tailWord_7536273, baseEnd_7536273] using wordTrace_append hprefix tailTrace_7536273
  have hstable : (prefixWord ++ tailWord_7536273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536273).length < 2 ^ (prefixWord ++ tailWord_7536273).sum := by decide
  have hdescent : baseEnd_7536273 < baseStart_7536273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536274 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7536274 : Nat := 118140960795 + 7536274 * 2 ^ 59
def prefixEnd_7536274 : Nat := 4983230072969 + 3 ^ 40 * 7536274 * 2
def baseEnd_7536274 : Nat := 3869730905981952527016313

theorem tailTrace_7536274 : CollatzResearch.WordTrace tailWord_7536274 prefixEnd_7536274 3869730905981952527016313 := by
  unfold tailWord_7536274
  simp only [CollatzResearch.WordTrace]
  refine ⟨68717623574843466493397969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183246996199582577315727917 68717623574843466493397969)
  ·
    refine ⟨51538217681132599870048477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68717623574843466493397969 51538217681132599870048477)
    ·
      refine ⟨19326831630424724951268179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51538217681132599870048477 19326831630424724951268179)
      ·
        refine ⟨28990247445637087426902269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19326831630424724951268179 28990247445637087426902269)
        ·
          refine ⟨10871342792113907785088351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28990247445637087426902269 10871342792113907785088351)
          ·
            refine ⟨16307014188170861677632527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871342792113907785088351 16307014188170861677632527)
            ·
              refine ⟨24460521282256292516448791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307014188170861677632527 24460521282256292516448791)
              ·
                refine ⟨36690781923384438774673187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24460521282256292516448791 36690781923384438774673187)
                ·
                  refine ⟨55036172885076658162009781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36690781923384438774673187 55036172885076658162009781)
                  ·
                    refine ⟨5159641207975936702688417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55036172885076658162009781 5159641207975936702688417)
                    ·
                      refine ⟨3869730905981952527016313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159641207975936702688417 3869730905981952527016313)
                      ·
                        rfl

theorem cell23_7536274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7536274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536274 prefixEnd_7536274 := by exact prefixLift 7536274
  have htrace : WordTrace (prefixWord ++ tailWord_7536274) baseStart_7536274 baseEnd_7536274 := by
    simpa [prefixWord, tailWord_7536274, baseEnd_7536274] using wordTrace_append hprefix tailTrace_7536274
  have hstable : (prefixWord ++ tailWord_7536274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536274).length < 2 ^ (prefixWord ++ tailWord_7536274).sum := by decide
  have hdescent : baseEnd_7536274 < baseStart_7536274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536280 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_7536280 : Nat := 118140960795 + 7536280 * 2 ^ 59
def prefixEnd_7536280 : Nat := 4983230072969 + 3 ^ 40 * 7536280 * 2
def baseEnd_7536280 : Nat := 1289911328955293167847095

theorem tailTrace_7536280 : CollatzResearch.WordTrace tailWord_7536280 prefixEnd_7536280 1289911328955293167847095 := by
  unfold tailWord_7536280
  simp only [CollatzResearch.WordTrace]
  refine ⟨137435356568676064499155147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183247142091568085998873529 137435356568676064499155147)
  ·
    refine ⟨206153034853014096748732721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137435356568676064499155147 206153034853014096748732721)
    ·
      refine ⟨154614776139760572561549541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206153034853014096748732721 154614776139760572561549541)
      ·
        refine ⟨28990270526205107355290539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154614776139760572561549541 28990270526205107355290539)
        ·
          refine ⟨43485405789307661032935809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28990270526205107355290539 43485405789307661032935809)
          ·
            refine ⟨32614054341980745774701857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43485405789307661032935809 32614054341980745774701857)
            ·
              refine ⟨24460540756485559331026393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32614054341980745774701857 24460540756485559331026393)
              ·
                refine ⟨18345405567364169498269795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24460540756485559331026393 18345405567364169498269795)
                ·
                  refine ⟨27518108351046254247404693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18345405567364169498269795 27518108351046254247404693)
                  ·
                    refine ⟨1289911328955293167847095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27518108351046254247404693 1289911328955293167847095)
                    ·
                      rfl

theorem cell23_7536280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_7536280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536280 prefixEnd_7536280 := by exact prefixLift 7536280
  have htrace : WordTrace (prefixWord ++ tailWord_7536280) baseStart_7536280 baseEnd_7536280 := by
    simpa [prefixWord, tailWord_7536280, baseEnd_7536280] using wordTrace_append hprefix tailTrace_7536280
  have hstable : (prefixWord ++ tailWord_7536280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536280).length < 2 ^ (prefixWord ++ tailWord_7536280).sum := by decide
  have hdescent : baseEnd_7536280 < baseStart_7536280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536314 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_7536314 : Nat := 118140960795 + 7536314 * 2 ^ 59
def prefixEnd_7536314 : Nat := 4983230072969 + 3 ^ 40 * 7536314 * 2
def baseEnd_7536314 : Nat := 1289917148402710790172043

theorem tailTrace_7536314 : CollatzResearch.WordTrace tailWord_7536314 prefixEnd_7536314 1289917148402710790172043 := by
  unfold tailWord_7536314
  simp only [CollatzResearch.WordTrace]
  refine ⟨68717988304807238201261999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183247968812819301870031997 68717988304807238201261999)
  ·
    refine ⟨103076982457210857301892999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68717988304807238201261999 103076982457210857301892999)
    ·
      refine ⟨154615473685816285952839499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103076982457210857301892999 154615473685816285952839499)
      ·
        refine ⟨231923210528724428929259249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154615473685816285952839499 231923210528724428929259249)
        ·
          refine ⟨173942407896543321696944437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231923210528724428929259249 173942407896543321696944437)
          ·
            refine ⟨16307100740300936409088541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173942407896543321696944437 16307100740300936409088541)
            ·
              refine ⟨6115162777612851153408203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16307100740300936409088541 6115162777612851153408203)
              ·
                refine ⟨9172744166419276730112305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115162777612851153408203 9172744166419276730112305)
                ·
                  refine ⟨6879558124814457547584229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9172744166419276730112305 6879558124814457547584229)
                  ·
                    refine ⟨1289917148402710790172043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6879558124814457547584229 1289917148402710790172043)
                    ·
                      rfl

theorem cell23_7536314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_7536314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536314 prefixEnd_7536314 := by exact prefixLift 7536314
  have htrace : WordTrace (prefixWord ++ tailWord_7536314) baseStart_7536314 baseEnd_7536314 := by
    simpa [prefixWord, tailWord_7536314, baseEnd_7536314] using wordTrace_append hprefix tailTrace_7536314
  have hstable : (prefixWord ++ tailWord_7536314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536314).length < 2 ^ (prefixWord ++ tailWord_7536314).sum := by decide
  have hdescent : baseEnd_7536314 < baseStart_7536314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536324 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_7536324 : Nat := 118140960795 + 7536324 * 2 ^ 59
def prefixEnd_7536324 : Nat := 4983230072969 + 3 ^ 40 * 7536324 * 2
def baseEnd_7536324 : Nat := 3869756580014677331391083

theorem tailTrace_7536324 : CollatzResearch.WordTrace tailWord_7536324 prefixEnd_7536324 3869756580014677331391083 := by
  unfold tailWord_7536324
  simp only [CollatzResearch.WordTrace]
  refine ⟨137436158974596362256456013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183248211966128483008608017 137436158974596362256456013)
  ·
    refine ⟨51538559615473635846171005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137436158974596362256456013 51538559615473635846171005)
    ·
      refine ⟨19326959855802613442314127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51538559615473635846171005 19326959855802613442314127)
      ·
        refine ⟨28990439783703920163471191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19326959855802613442314127 28990439783703920163471191)
        ·
          refine ⟨43485659675555880245206787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28990439783703920163471191 43485659675555880245206787)
          ·
            refine ⟨65228489513333820367810181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43485659675555880245206787 65228489513333820367810181)
            ·
              refine ⟨12230341783750091318964409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65228489513333820367810181 12230341783750091318964409)
              ·
                refine ⟨9172756337812568489223307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12230341783750091318964409 9172756337812568489223307)
                ·
                  refine ⟨13759134506718852733834961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172756337812568489223307 13759134506718852733834961)
                  ·
                    refine ⟨10319350880039139550376221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13759134506718852733834961 10319350880039139550376221)
                    ·
                      refine ⟨3869756580014677331391083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10319350880039139550376221 3869756580014677331391083)
                      ·
                        rfl

theorem cell23_7536324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_7536324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536324 prefixEnd_7536324 := by exact prefixLift 7536324
  have htrace : WordTrace (prefixWord ++ tailWord_7536324) baseStart_7536324 baseEnd_7536324 := by
    simpa [prefixWord, tailWord_7536324, baseEnd_7536324] using wordTrace_append hprefix tailTrace_7536324
  have hstable : (prefixWord ++ tailWord_7536324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536324).length < 2 ^ (prefixWord ++ tailWord_7536324).sum := by decide
  have hdescent : baseEnd_7536324 < baseStart_7536324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536337 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_7536337 : Nat := 118140960795 + 7536337 * 2 ^ 59
def prefixEnd_7536337 : Nat := 4983230072969 + 3 ^ 40 * 7536337 * 2
def baseEnd_7536337 : Nat := 3869763255263185780528523

theorem tailTrace_7536337 : CollatzResearch.WordTrace tailWord_7536337 prefixEnd_7536337 3869763255263185780528523 := by
  unfold tailWord_7536337
  simp only [CollatzResearch.WordTrace]
  refine ⟨274872792098145627733135265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183248528065430418488756843 274872792098145627733135265)
  ·
    refine ⟨206154594073609220799851449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274872792098145627733135265 206154594073609220799851449)
    ·
      refine ⟨154615945555206915599888587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206154594073609220799851449 154615945555206915599888587)
      ·
        refine ⟨231923918332810373399832881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154615945555206915599888587 231923918332810373399832881)
        ·
          refine ⟨173942938749607780049874661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231923918332810373399832881 173942938749607780049874661)
          ·
            refine ⟨32614301015551458759351499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173942938749607780049874661 32614301015551458759351499)
            ·
              refine ⟨48921451523327188139027249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32614301015551458759351499 48921451523327188139027249)
              ·
                refine ⟨36691088642495391104270437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48921451523327188139027249 36691088642495391104270437)
                ·
                  refine ⟨6879579120467885832050707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36691088642495391104270437 6879579120467885832050707)
                  ·
                    refine ⟨10319368680701828748076061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6879579120467885832050707 10319368680701828748076061)
                    ·
                      refine ⟨3869763255263185780528523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10319368680701828748076061 3869763255263185780528523)
                      ·
                        rfl

theorem cell23_7536337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_7536337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536337 prefixEnd_7536337 := by exact prefixLift 7536337
  have htrace : WordTrace (prefixWord ++ tailWord_7536337) baseStart_7536337 baseEnd_7536337 := by
    simpa [prefixWord, tailWord_7536337, baseEnd_7536337] using wordTrace_append hprefix tailTrace_7536337
  have hstable : (prefixWord ++ tailWord_7536337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536337).length < 2 ^ (prefixWord ++ tailWord_7536337).sum := by decide
  have hdescent : baseEnd_7536337 < baseStart_7536337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536338 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7536338 : Nat := 118140960795 + 7536338 * 2 ^ 59
def prefixEnd_7536338 : Nat := 4983230072969 + 3 ^ 40 * 7536338 * 2
def baseEnd_7536338 : Nat := 3869763768743840276616019

theorem tailTrace_7536338 : CollatzResearch.WordTrace tailWord_7536338 prefixEnd_7536338 3869763768743840276616019 := by
  unfold tailWord_7536338
  simp only [CollatzResearch.WordTrace]
  refine ⟨68718207142785501225980417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183248552380761336602614445 68718207142785501225980417)
  ·
    refine ⟨51538655357089125919485313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68718207142785501225980417 51538655357089125919485313)
    ·
      refine ⟨38653991517816844439613985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51538655357089125919485313 38653991517816844439613985)
      ·
        refine ⟨28990493638362633329710489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38653991517816844439613985 28990493638362633329710489)
        ·
          refine ⟨21742870228771974997282867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28990493638362633329710489 21742870228771974997282867)
          ·
            refine ⟨32614305343157962495924301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21742870228771974997282867 32614305343157962495924301)
            ·
              refine ⟨12230364503684235935971613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32614305343157962495924301 12230364503684235935971613)
              ·
                refine ⟨4586386688881588475989355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12230364503684235935971613 4586386688881588475989355)
                ·
                  refine ⟨6879580033322382713984033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586386688881588475989355 6879580033322382713984033)
                  ·
                    refine ⟨5159685024991787035488025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879580033322382713984033 5159685024991787035488025)
                    ·
                      refine ⟨3869763768743840276616019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159685024991787035488025 3869763768743840276616019)
                      ·
                        rfl

theorem cell23_7536338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7536338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536338 prefixEnd_7536338 := by exact prefixLift 7536338
  have htrace : WordTrace (prefixWord ++ tailWord_7536338) baseStart_7536338 baseEnd_7536338 := by
    simpa [prefixWord, tailWord_7536338, baseEnd_7536338] using wordTrace_append hprefix tailTrace_7536338
  have hstable : (prefixWord ++ tailWord_7536338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536338).length < 2 ^ (prefixWord ++ tailWord_7536338).sum := by decide
  have hdescent : baseEnd_7536338 < baseStart_7536338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536355 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7536355 : Nat := 118140960795 + 7536355 * 2 ^ 59
def prefixEnd_7536355 : Nat := 4983230072969 + 3 ^ 40 * 7536355 * 2
def baseEnd_7536355 : Nat := 3869772497914966710103441

theorem tailTrace_7536355 : CollatzResearch.WordTrace tailWord_7536355 prefixEnd_7536355 3869772497914966710103441 := by
  unfold tailWord_7536355
  simp only [CollatzResearch.WordTrace]
  refine ⟨274873448612080416807290519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183248965741386944538193679 274873448612080416807290519)
  ·
    refine ⟨412310172918120625210935779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274873448612080416807290519 412310172918120625210935779)
    ·
      refine ⟨618465259377180937816403669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412310172918120625210935779 618465259377180937816403669)
      ·
        refine ⟨14495279516652678230071961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 618465259377180937816403669 14495279516652678230071961)
        ·
          refine ⟨10871459637489508672553971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14495279516652678230071961 10871459637489508672553971)
          ·
            refine ⟨16307189456234263008830957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871459637489508672553971 16307189456234263008830957)
            ·
              refine ⟨6115196046087848628311609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16307189456234263008830957 6115196046087848628311609)
              ·
                refine ⟨4586397034565886471233707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115196046087848628311609 4586397034565886471233707)
                ·
                  refine ⟨6879595551848829706850561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586397034565886471233707 6879595551848829706850561)
                  ·
                    refine ⟨5159696663886622280137921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879595551848829706850561 5159696663886622280137921)
                    ·
                      refine ⟨3869772497914966710103441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159696663886622280137921 3869772497914966710103441)
                      ·
                        rfl

theorem cell23_7536355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7536355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536355 prefixEnd_7536355 := by exact prefixLift 7536355
  have htrace : WordTrace (prefixWord ++ tailWord_7536355) baseStart_7536355 baseEnd_7536355 := by
    simpa [prefixWord, tailWord_7536355, baseEnd_7536355] using wordTrace_append hprefix tailTrace_7536355
  have hstable : (prefixWord ++ tailWord_7536355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536355).length < 2 ^ (prefixWord ++ tailWord_7536355).sum := by decide
  have hdescent : baseEnd_7536355 < baseStart_7536355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536370 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_7536370 : Nat := 118140960795 + 7536370 * 2 ^ 59
def prefixEnd_7536370 : Nat := 4983230072969 + 3 ^ 40 * 7536370 * 2
def baseEnd_7536370 : Nat := 1289926733374928050471957

theorem tailTrace_7536370 : CollatzResearch.WordTrace tailWord_7536370 prefixEnd_7536370 1289926733374928050471957 := by
  unfold tailWord_7536370
  simp only [CollatzResearch.WordTrace]
  refine ⟨68718498926756518592271641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183249330471350716246057709 68718498926756518592271641)
  ·
    refine ⟨51538874195067388944203731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68718498926756518592271641 51538874195067388944203731)
    ·
      refine ⟨77308311292601083416305597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51538874195067388944203731 77308311292601083416305597)
      ·
        refine ⟨28990616734725406281114599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77308311292601083416305597 28990616734725406281114599)
        ·
          refine ⟨43485925102088109421671899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28990616734725406281114599 43485925102088109421671899)
          ·
            refine ⟨65228887653132164132507849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43485925102088109421671899 65228887653132164132507849)
            ·
              refine ⟨48921665739849123099380887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65228887653132164132507849 48921665739849123099380887)
              ·
                refine ⟨73382498609773684649071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48921665739849123099380887 73382498609773684649071331)
                ·
                  refine ⟨110073747914660526973606997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73382498609773684649071331 110073747914660526973606997)
                  ·
                    refine ⟨1289926733374928050471957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110073747914660526973606997 1289926733374928050471957)
                    ·
                      rfl

theorem cell23_7536370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_7536370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536370 prefixEnd_7536370 := by exact prefixLift 7536370
  have htrace : WordTrace (prefixWord ++ tailWord_7536370) baseStart_7536370 baseEnd_7536370 := by
    simpa [prefixWord, tailWord_7536370, baseEnd_7536370] using wordTrace_append hprefix tailTrace_7536370
  have hstable : (prefixWord ++ tailWord_7536370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536370).length < 2 ^ (prefixWord ++ tailWord_7536370).sum := by decide
  have hdescent : baseEnd_7536370 < baseStart_7536370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536380 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7536380 : Nat := 118140960795 + 7536380 * 2 ^ 59
def prefixEnd_7536380 : Nat := 4983230072969 + 3 ^ 40 * 7536380 * 2
def baseEnd_7536380 : Nat := 3869785334931329112290825

theorem tailTrace_7536380 : CollatzResearch.WordTrace tailWord_7536380 prefixEnd_7536380 3869785334931329112290825 := by
  unfold tailWord_7536380
  simp only [CollatzResearch.WordTrace]
  refine ⟨137437180218494923038475297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183249573624659897384633729 137437180218494923038475297)
  ·
    refine ⟨103077885163871192278856473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137437180218494923038475297 103077885163871192278856473)
    ·
      refine ⟨77308413872903394209142355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103077885163871192278856473 77308413872903394209142355)
      ·
        refine ⟨115962620809355091313713533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77308413872903394209142355 115962620809355091313713533)
        ·
          refine ⟨43485982803508159242642575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115962620809355091313713533 43485982803508159242642575)
          ·
            refine ⟨65228974205262238863963863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43485982803508159242642575 65228974205262238863963863)
            ·
              refine ⟨97843461307893358295945795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65228974205262238863963863 97843461307893358295945795)
              ·
                refine ⟨146765191961840037443918693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97843461307893358295945795 146765191961840037443918693)
                ·
                  refine ⟨27518473492845007020734755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146765191961840037443918693 27518473492845007020734755)
                  ·
                    refine ⟨41277710239267510531102133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27518473492845007020734755 41277710239267510531102133)
                    ·
                      refine ⟨3869785334931329112290825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41277710239267510531102133 3869785334931329112290825)
                      ·
                        rfl

theorem cell23_7536380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7536380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536380 prefixEnd_7536380 := by exact prefixLift 7536380
  have htrace : WordTrace (prefixWord ++ tailWord_7536380) baseStart_7536380 baseEnd_7536380 := by
    simpa [prefixWord, tailWord_7536380, baseEnd_7536380] using wordTrace_append hprefix tailTrace_7536380
  have hstable : (prefixWord ++ tailWord_7536380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536380).length < 2 ^ (prefixWord ++ tailWord_7536380).sum := by decide
  have hdescent : baseEnd_7536380 < baseStart_7536380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536394 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2]
def baseStart_7536394 : Nat := 118140960795 + 7536394 * 2 ^ 59
def prefixEnd_7536394 : Nat := 4983230072969 + 3 ^ 40 * 7536394 * 2
def baseEnd_7536394 : Nat := 3869792523660492057515761

theorem tailTrace_7536394 : CollatzResearch.WordTrace tailWord_7536394 prefixEnd_7536394 3869792523660492057515761 := by
  unfold tailWord_7536394
  simp only [CollatzResearch.WordTrace]
  refine ⟨68718717764734781616990059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183249914039292750978640157 68718717764734781616990059)
  ·
    refine ⟨103078076647102172425485089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68718717764734781616990059 103078076647102172425485089)
    ·
      refine ⟨77308557485326629319113817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103078076647102172425485089 77308557485326629319113817)
      ·
        refine ⟨57981418113994971989335363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77308557485326629319113817 57981418113994971989335363)
        ·
          refine ⟨86972127170992457984003045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57981418113994971989335363 86972127170992457984003045)
          ·
            refine ⟨16307273844561085872000571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86972127170992457984003045 16307273844561085872000571)
            ·
              refine ⟨24460910766841628808000857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307273844561085872000571 24460910766841628808000857)
              ·
                refine ⟨18345683075131221606000643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24460910766841628808000857 18345683075131221606000643)
                ·
                  refine ⟨27518524612696832409000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18345683075131221606000643 27518524612696832409000965)
                  ·
                    refine ⟨5159723364880656076687681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27518524612696832409000965 5159723364880656076687681)
                    ·
                      refine ⟨3869792523660492057515761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159723364880656076687681 3869792523660492057515761)
                      ·
                        rfl

theorem cell23_7536394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_7536394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536394 prefixEnd_7536394 := by exact prefixLift 7536394
  have htrace : WordTrace (prefixWord ++ tailWord_7536394) baseStart_7536394 baseEnd_7536394 := by
    simpa [prefixWord, tailWord_7536394, baseEnd_7536394] using wordTrace_append hprefix tailTrace_7536394
  have hstable : (prefixWord ++ tailWord_7536394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536394).length < 2 ^ (prefixWord ++ tailWord_7536394).sum := by decide
  have hdescent : baseEnd_7536394 < baseStart_7536394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536447 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 7]
def baseStart_7536447 : Nat := 118140960795 + 7536447 * 2 ^ 59
def prefixEnd_7536447 : Nat := 4983230072969 + 3 ^ 40 * 7536447 * 2
def baseEnd_7536447 : Nat := 1289939912711726783384339

theorem tailTrace_7536447 : CollatzResearch.WordTrace tailWord_7536447 prefixEnd_7536447 1289939912711726783384339 := by
  unfold tailWord_7536447
  simp only [CollatzResearch.WordTrace]
  refine ⟨274876804127747116519639595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183251202751831411013093063 274876804127747116519639595)
  ·
    refine ⟨412315206191620674779459393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274876804127747116519639595 412315206191620674779459393)
    ·
      refine ⟨309236404643715506084594545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412315206191620674779459393 309236404643715506084594545)
      ·
        refine ⟨231927303482786629563445909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309236404643715506084594545 231927303482786629563445909)
        ·
          refine ⟨10871592350755623260786527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231927303482786629563445909 10871592350755623260786527)
          ·
            refine ⟨16307388526133434891179791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871592350755623260786527 16307388526133434891179791)
            ·
              refine ⟨24461082789200152336769687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16307388526133434891179791 24461082789200152336769687)
              ·
                refine ⟨36691624183800228505154531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24461082789200152336769687 36691624183800228505154531)
                ·
                  refine ⟨55037436275700342757731797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36691624183800228505154531 55037436275700342757731797)
                  ·
                    refine ⟨1289939912711726783384339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55037436275700342757731797 1289939912711726783384339)
                    ·
                      rfl

theorem cell23_7536447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_7536447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536447 prefixEnd_7536447 := by exact prefixLift 7536447
  have htrace : WordTrace (prefixWord ++ tailWord_7536447) baseStart_7536447 baseEnd_7536447 := by
    simpa [prefixWord, tailWord_7536447, baseEnd_7536447] using wordTrace_append hprefix tailTrace_7536447
  have hstable : (prefixWord ++ tailWord_7536447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536447).length < 2 ^ (prefixWord ++ tailWord_7536447).sum := by decide
  have hdescent : baseEnd_7536447 < baseStart_7536447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536487 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_7536487 : Nat := 118140960795 + 7536487 * 2 ^ 59
def prefixEnd_7536487 : Nat := 4983230072969 + 3 ^ 40 * 7536487 * 2
def baseEnd_7536487 : Nat := 3869840277361360193652833

theorem tailTrace_7536487 : CollatzResearch.WordTrace tailWord_7536487 prefixEnd_7536487 3869840277361360193652833 := by
  unfold tailWord_7536487
  simp only [CollatzResearch.WordTrace]
  refine ⟨274878263047602203351095715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183252175365068135567397143 274878263047602203351095715)
  ·
    refine ⟨412317394571403305026643573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274878263047602203351095715 412317394571403305026643573)
    ·
      refine ⟨38654755741069059846247835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 412317394571403305026643573 38654755741069059846247835)
      ·
        refine ⟨57982133611603589769371753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38654755741069059846247835 57982133611603589769371753)
        ·
          refine ⟨43486600208702692327028815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57982133611603589769371753 43486600208702692327028815)
          ·
            refine ⟨65229900313054038490543223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43486600208702692327028815 65229900313054038490543223)
            ·
              refine ⟨97844850469581057735814835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65229900313054038490543223 97844850469581057735814835)
              ·
                refine ⟨146767275704371586603722253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97844850469581057735814835 146767275704371586603722253)
                ·
                  refine ⟨55037728389139344976395845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146767275704371586603722253 55037728389139344976395845)
                  ·
                    refine ⟨10319574072963627183074221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55037728389139344976395845 10319574072963627183074221)
                    ·
                      refine ⟨3869840277361360193652833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10319574072963627183074221 3869840277361360193652833)
                      ·
                        rfl

theorem cell23_7536487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_7536487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536487 prefixEnd_7536487 := by exact prefixLift 7536487
  have htrace : WordTrace (prefixWord ++ tailWord_7536487) baseStart_7536487 baseEnd_7536487 := by
    simpa [prefixWord, tailWord_7536487, baseEnd_7536487] using wordTrace_append hprefix tailTrace_7536487
  have hstable : (prefixWord ++ tailWord_7536487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536487).length < 2 ^ (prefixWord ++ tailWord_7536487).sum := by decide
  have hdescent : baseEnd_7536487 < baseStart_7536487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536541 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 6]
def baseStart_7536541 : Nat := 118140960795 + 7536541 * 2 ^ 59
def prefixEnd_7536541 : Nat := 4983230072969 + 3 ^ 40 * 7536541 * 2
def baseEnd_7536541 : Nat := 429985333924078109153065

theorem tailTrace_7536541 : CollatzResearch.WordTrace tailWord_7536541 prefixEnd_7536541 429985333924078109153065 := by
  unfold tailWord_7536541
  simp only [CollatzResearch.WordTrace]
  refine ⟨274880232589406570573561477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183253488392937713715707651 274880232589406570573561477)
  ·
    refine ⟨51540043610513731982542777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274880232589406570573561477 51540043610513731982542777)
    ·
      refine ⟨38655032707885298986907083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51540043610513731982542777 38655032707885298986907083)
      ·
        refine ⟨57982549061827948480360625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38655032707885298986907083 57982549061827948480360625)
        ·
          refine ⟨43486911796370961360270469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57982549061827948480360625 43486911796370961360270469)
          ·
            refine ⟨8153795961819555255050713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43486911796370961360270469 8153795961819555255050713)
            ·
              refine ⟨6115346971364666441288035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153795961819555255050713 6115346971364666441288035)
              ·
                refine ⟨9173020457046999661932053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115346971364666441288035 9173020457046999661932053)
                ·
                  refine ⟨429985333924078109153065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9173020457046999661932053 429985333924078109153065)
                  ·
                    rfl

theorem cell23_7536541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_7536541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536541 prefixEnd_7536541 := by exact prefixLift 7536541
  have htrace : WordTrace (prefixWord ++ tailWord_7536541) baseStart_7536541 baseEnd_7536541 := by
    simpa [prefixWord, tailWord_7536541, baseEnd_7536541] using wordTrace_append hprefix tailTrace_7536541
  have hstable : (prefixWord ++ tailWord_7536541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536541).length < 2 ^ (prefixWord ++ tailWord_7536541).sum := by decide
  have hdescent : baseEnd_7536541 < baseStart_7536541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536544 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2]
def baseStart_7536544 : Nat := 118140960795 + 7536544 * 2 ^ 59
def prefixEnd_7536544 : Nat := 4983230072969 + 3 ^ 40 * 7536544 * 2
def baseEnd_7536544 : Nat := 3869869545758666470640071

theorem tailTrace_7536544 : CollatzResearch.WordTrace tailWord_7536544 prefixEnd_7536544 3869869545758666470640071 := by
  unfold tailWord_7536544
  simp only [CollatzResearch.WordTrace]
  refine ⟨137440171004197851042960343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183253561338930468057280457 137440171004197851042960343)
  ·
    refine ⟨206160256506296776564440515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137440171004197851042960343 206160256506296776564440515)
    ·
      refine ⟨309240384759445164846660773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206160256506296776564440515 309240384759445164846660773)
      ·
        refine ⟨57982572142395968408748895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309240384759445164846660773 57982572142395968408748895)
        ·
          refine ⟨86973858213593952613123343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57982572142395968408748895 86973858213593952613123343)
          ·
            refine ⟨130460787320390928919685015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86973858213593952613123343 130460787320390928919685015)
            ·
              refine ⟨195691180980586393379527523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130460787320390928919685015 195691180980586393379527523)
              ·
                refine ⟨293536771470879590069291285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195691180980586393379527523 293536771470879590069291285)
                ·
                  refine ⟨13759536162697480784498029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293536771470879590069291285 13759536162697480784498029)
                  ·
                    refine ⟨5159826061011555294186761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13759536162697480784498029 5159826061011555294186761)
                    ·
                      refine ⟨3869869545758666470640071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159826061011555294186761 3869869545758666470640071)
                      ·
                        rfl

theorem cell23_7536544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_7536544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536544 prefixEnd_7536544 := by exact prefixLift 7536544
  have htrace : WordTrace (prefixWord ++ tailWord_7536544) baseStart_7536544 baseEnd_7536544 := by
    simpa [prefixWord, tailWord_7536544, baseEnd_7536544] using wordTrace_append hprefix tailTrace_7536544
  have hstable : (prefixWord ++ tailWord_7536544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536544).length < 2 ^ (prefixWord ++ tailWord_7536544).sum := by decide
  have hdescent : baseEnd_7536544 < baseStart_7536544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536561 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7536561 : Nat := 118140960795 + 7536561 * 2 ^ 59
def prefixEnd_7536561 : Nat := 4983230072969 + 3 ^ 40 * 7536561 * 2
def baseEnd_7536561 : Nat := 3869878274929792904127493

theorem tailTrace_7536561 : CollatzResearch.WordTrace tailWord_7536561 prefixEnd_7536561 3869878274929792904127493 := by
  unfold tailWord_7536561
  simp only [CollatzResearch.WordTrace]
  refine ⟨274880962049334113989289537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183253974699556075992859691 274880962049334113989289537)
  ·
    refine ⟨206160721537000585491967153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274880962049334113989289537 206160721537000585491967153)
    ·
      refine ⟨154620541152750439118975365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206160721537000585491967153 154620541152750439118975365)
      ·
        refine ⟨28991351466140707334807881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154620541152750439118975365 28991351466140707334807881)
        ·
          refine ⟨21743513599605530501105911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28991351466140707334807881 21743513599605530501105911)
          ·
            refine ⟨32615270399408295751658867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21743513599605530501105911 32615270399408295751658867)
            ·
              refine ⟨48922905599112443627488301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32615270399408295751658867 48922905599112443627488301)
              ·
                refine ⟨18346089599667166360308113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48922905599112443627488301 18346089599667166360308113)
                ·
                  refine ⟨13759567199750374770231085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18346089599667166360308113 13759567199750374770231085)
                  ·
                    refine ⟨5159837699906390538836657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13759567199750374770231085 5159837699906390538836657)
                    ·
                      refine ⟨3869878274929792904127493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159837699906390538836657 3869878274929792904127493)
                      ·
                        rfl

theorem cell23_7536561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7536561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536561 prefixEnd_7536561 := by exact prefixLift 7536561
  have htrace : WordTrace (prefixWord ++ tailWord_7536561) baseStart_7536561 baseEnd_7536561 := by
    simpa [prefixWord, tailWord_7536561, baseEnd_7536561] using wordTrace_append hprefix tailTrace_7536561
  have hstable : (prefixWord ++ tailWord_7536561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536561).length < 2 ^ (prefixWord ++ tailWord_7536561).sum := by decide
  have hdescent : baseEnd_7536561 < baseStart_7536561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536587 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_7536587 : Nat := 118140960795 + 7536587 * 2 ^ 59
def prefixEnd_7536587 : Nat := 4983230072969 + 3 ^ 40 * 7536587 * 2
def baseEnd_7536587 : Nat := 3869891625426809802402373

theorem tailTrace_7536587 : CollatzResearch.WordTrace tailWord_7536587 prefixEnd_7536587 3869891625426809802402373 := by
  unfold tailWord_7536587
  simp only [CollatzResearch.WordTrace]
  refine ⟨274881910347239920429736015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183254606898159946953157343 274881910347239920429736015)
  ·
    refine ⟨412322865520859880644604023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274881910347239920429736015 412322865520859880644604023)
    ·
      refine ⟨618484298281289820966906035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412322865520859880644604023 618484298281289820966906035)
      ·
        refine ⟨927726447421934731450359053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618484298281289820966906035 927726447421934731450359053)
        ·
          refine ⟨347897417783225524293884645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927726447421934731450359053 347897417783225524293884645)
          ·
            refine ⟨65230765834354785805103371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347897417783225524293884645 65230765834354785805103371)
            ·
              refine ⟨97846148751532178707655057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65230765834354785805103371 97846148751532178707655057)
              ·
                refine ⟨73384611563649134030741293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97846148751532178707655057 73384611563649134030741293)
                ·
                  refine ⟨27519229336368425261527985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73384611563649134030741293 27519229336368425261527985)
                  ·
                    refine ⟨20639422002276318946145989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27519229336368425261527985 20639422002276318946145989)
                    ·
                      refine ⟨3869891625426809802402373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20639422002276318946145989 3869891625426809802402373)
                      ·
                        rfl

theorem cell23_7536587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_7536587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536587 prefixEnd_7536587 := by exact prefixLift 7536587
  have htrace : WordTrace (prefixWord ++ tailWord_7536587) baseStart_7536587 baseEnd_7536587 := by
    simpa [prefixWord, tailWord_7536587, baseEnd_7536587] using wordTrace_append hprefix tailTrace_7536587
  have hstable : (prefixWord ++ tailWord_7536587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536587).length < 2 ^ (prefixWord ++ tailWord_7536587).sum := by decide
  have hdescent : baseEnd_7536587 < baseStart_7536587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536591 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 3, 2, 2]
def baseStart_7536591 : Nat := 118140960795 + 7536591 * 2 ^ 59
def prefixEnd_7536591 : Nat := 4983230072969 + 3 ^ 40 * 7536591 * 2
def baseEnd_7536591 : Nat := 3869893679349427786752355

theorem tailTrace_7536591 : CollatzResearch.WordTrace tailWord_7536591 prefixEnd_7536591 3869893679349427786752355 := by
  unfold tailWord_7536591
  simp only [CollatzResearch.WordTrace]
  refine ⟨274882056239225429112881627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183254704159483619408587751 274882056239225429112881627)
  ·
    refine ⟨412323084358838143669322441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274882056239225429112881627 412323084358838143669322441)
    ·
      refine ⟨309242313269128607751991831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412323084358838143669322441 309242313269128607751991831)
      ·
        refine ⟨463863469903692911627987747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309242313269128607751991831 463863469903692911627987747)
        ·
          refine ⟨695795204855539367441981621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463863469903692911627987747 695795204855539367441981621)
          ·
            refine ⟨65230800455206815697685777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 695795204855539367441981621 65230800455206815697685777)
            ·
              refine ⟨48923100341405111773264333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65230800455206815697685777 48923100341405111773264333)
              ·
                refine ⟨18346162628026916914974125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48923100341405111773264333 18346162628026916914974125)
                ·
                  refine ⟨6879810985510093843115297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18346162628026916914974125 6879810985510093843115297)
                  ·
                    refine ⟨5159858239132570382336473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879810985510093843115297 5159858239132570382336473)
                    ·
                      refine ⟨3869893679349427786752355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159858239132570382336473 3869893679349427786752355)
                      ·
                        rfl

theorem cell23_7536591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 2, 2].length) (baseStart_7536591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536591 prefixEnd_7536591 := by exact prefixLift 7536591
  have htrace : WordTrace (prefixWord ++ tailWord_7536591) baseStart_7536591 baseEnd_7536591 := by
    simpa [prefixWord, tailWord_7536591, baseEnd_7536591] using wordTrace_append hprefix tailTrace_7536591
  have hstable : (prefixWord ++ tailWord_7536591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536591).length < 2 ^ (prefixWord ++ tailWord_7536591).sum := by decide
  have hdescent : baseEnd_7536591 < baseStart_7536591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536624 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_7536624 : Nat := 118140960795 + 7536624 * 2 ^ 59
def prefixEnd_7536624 : Nat := 4983230072969 + 3 ^ 40 * 7536624 * 2
def baseEnd_7536624 : Nat := 3869910624211026157639703

theorem tailTrace_7536624 : CollatzResearch.WordTrace tailWord_7536624 prefixEnd_7536624 3869910624211026157639703 := by
  unfold tailWord_7536624
  simp only [CollatzResearch.WordTrace]
  refine ⟨137441629924052937874416463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183255506565403917165888617 137441629924052937874416463)
  ·
    refine ⟨206162444886079406811624695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137441629924052937874416463 206162444886079406811624695)
    ·
      refine ⟨309243667329119110217437043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206162444886079406811624695 309243667329119110217437043)
      ·
        refine ⟨463865500993678665326155565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309243667329119110217437043 463865500993678665326155565)
        ·
          refine ⟨173949562872629499497308337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463865500993678665326155565 173949562872629499497308337)
          ·
            refine ⟨130462172154472124622981253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173949562872629499497308337 130462172154472124622981253)
            ·
              refine ⟨24461657278963523366808985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130462172154472124622981253 24461657278963523366808985)
              ·
                refine ⟨18346242959222642525106739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24461657278963523366808985 18346242959222642525106739)
                ·
                  refine ⟨27519364438833963787660109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18346242959222642525106739 27519364438833963787660109)
                  ·
                    refine ⟨10319761664562736420372541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27519364438833963787660109 10319761664562736420372541)
                    ·
                      refine ⟨3869910624211026157639703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10319761664562736420372541 3869910624211026157639703)
                      ·
                        rfl

theorem cell23_7536624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_7536624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536624 prefixEnd_7536624 := by exact prefixLift 7536624
  have htrace : WordTrace (prefixWord ++ tailWord_7536624) baseStart_7536624 baseEnd_7536624 := by
    simpa [prefixWord, tailWord_7536624, baseEnd_7536624] using wordTrace_append hprefix tailTrace_7536624
  have hstable : (prefixWord ++ tailWord_7536624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536624).length < 2 ^ (prefixWord ++ tailWord_7536624).sum := by decide
  have hdescent : baseEnd_7536624 < baseStart_7536624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536625 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_7536625 : Nat := 118140960795 + 7536625 * 2 ^ 59
def prefixEnd_7536625 : Nat := 4983230072969 + 3 ^ 40 * 7536625 * 2
def baseEnd_7536625 : Nat := 3869911137691680653727199

theorem tailTrace_7536625 : CollatzResearch.WordTrace tailWord_7536625 prefixEnd_7536625 3869911137691680653727199 := by
  unfold tailWord_7536625
  simp only [CollatzResearch.WordTrace]
  refine ⟨274883296321102252919619329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183255530880734835279746219 274883296321102252919619329)
  ·
    refine ⟨206162472240826689689714497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274883296321102252919619329 206162472240826689689714497)
    ·
      refine ⟨154621854180620017267285873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206162472240826689689714497 154621854180620017267285873)
      ·
        refine ⟨115966390635465012950464405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154621854180620017267285873 115966390635465012950464405)
        ·
          refine ⟨5435924561037422482053019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115966390635465012950464405 5435924561037422482053019)
          ·
            refine ⟨8153886841556133723079529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435924561037422482053019 8153886841556133723079529)
            ·
              refine ⟨6115415131167100292309647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8153886841556133723079529 6115415131167100292309647)
              ·
                refine ⟨9173122696750650438464471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115415131167100292309647 9173122696750650438464471)
                ·
                  refine ⟨13759684045125975657696707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173122696750650438464471 13759684045125975657696707)
                  ·
                    refine ⟨20639526067688963486545061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13759684045125975657696707 20639526067688963486545061)
                    ·
                      refine ⟨3869911137691680653727199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20639526067688963486545061 3869911137691680653727199)
                      ·
                        rfl

theorem cell23_7536625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_7536625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536625 prefixEnd_7536625 := by exact prefixLift 7536625
  have htrace : WordTrace (prefixWord ++ tailWord_7536625) baseStart_7536625 baseEnd_7536625 := by
    simpa [prefixWord, tailWord_7536625, baseEnd_7536625] using wordTrace_append hprefix tailTrace_7536625
  have hstable : (prefixWord ++ tailWord_7536625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536625).length < 2 ^ (prefixWord ++ tailWord_7536625).sum := by decide
  have hdescent : baseEnd_7536625 < baseStart_7536625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536641 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_7536641 : Nat := 118140960795 + 7536641 * 2 ^ 59
def prefixEnd_7536641 : Nat := 4983230072969 + 3 ^ 40 * 7536641 * 2
def baseEnd_7536641 : Nat := 3869919353382152591127125

theorem tailTrace_7536641 : CollatzResearch.WordTrace tailWord_7536641 prefixEnd_7536641 3869919353382152591127125 := by
  unfold tailWord_7536641
  simp only [CollatzResearch.WordTrace]
  refine ⟨274883879889044287652201777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183255919926029525101467851 274883879889044287652201777)
  ·
    refine ⟨206162909916783215739151333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274883879889044287652201777 206162909916783215739151333)
    ·
      refine ⟨38655545609396852951090875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206162909916783215739151333 38655545609396852951090875)
      ·
        refine ⟨57983318414095279426636313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38655545609396852951090875 57983318414095279426636313)
        ·
          refine ⟨43487488810571459569977235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57983318414095279426636313 43487488810571459569977235)
          ·
            refine ⟨65231233215857189354965853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43487488810571459569977235 65231233215857189354965853)
            ·
              refine ⟨24461712455946446008112195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65231233215857189354965853 24461712455946446008112195)
              ·
                refine ⟨36692568683919669012168293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24461712455946446008112195 36692568683919669012168293)
                ·
                  refine ⟨6879856628234937939781555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36692568683919669012168293 6879856628234937939781555)
                  ·
                    refine ⟨10319784942352406909672333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6879856628234937939781555 10319784942352406909672333)
                    ·
                      refine ⟨3869919353382152591127125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10319784942352406909672333 3869919353382152591127125)
                      ·
                        rfl

theorem cell23_7536641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_7536641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536641 prefixEnd_7536641 := by exact prefixLift 7536641
  have htrace : WordTrace (prefixWord ++ tailWord_7536641) baseStart_7536641 baseEnd_7536641 := by
    simpa [prefixWord, tailWord_7536641, baseEnd_7536641] using wordTrace_append hprefix tailTrace_7536641
  have hstable : (prefixWord ++ tailWord_7536641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536641).length < 2 ^ (prefixWord ++ tailWord_7536641).sum := by decide
  have hdescent : baseEnd_7536641 < baseStart_7536641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536668 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_7536668 : Nat := 118140960795 + 7536668 * 2 ^ 59
def prefixEnd_7536668 : Nat := 4983230072969 + 3 ^ 40 * 7536668 * 2
def baseEnd_7536668 : Nat := 3869933217359823985489501

theorem tailTrace_7536668 : CollatzResearch.WordTrace tailWord_7536668 prefixEnd_7536668 3869933217359823985489501 := by
  unfold tailWord_7536668
  simp only [CollatzResearch.WordTrace]
  refine ⟨137442432329973235631717329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183256576439964314175623105 137442432329973235631717329)
  ·
    refine ⟨103081824247479926723787997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137442432329973235631717329 103081824247479926723787997)
    ·
      refine ⟨38655684092804972521420499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103081824247479926723787997 38655684092804972521420499)
      ·
        refine ⟨57983526139207458782130749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38655684092804972521420499 57983526139207458782130749)
        ·
          refine ⟨21743822302202797043299031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57983526139207458782130749 21743822302202797043299031)
          ·
            refine ⟨32615733453304195564948547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21743822302202797043299031 32615733453304195564948547)
            ·
              refine ⟨48923600179956293347422821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32615733453304195564948547 48923600179956293347422821)
              ·
                refine ⟨9173175033741805002641779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48923600179956293347422821 9173175033741805002641779)
                ·
                  refine ⟨13759762550612707503962669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173175033741805002641779 13759762550612707503962669)
                  ·
                    refine ⟨5159910956479765313986001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13759762550612707503962669 5159910956479765313986001)
                    ·
                      refine ⟨3869933217359823985489501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159910956479765313986001 3869933217359823985489501)
                      ·
                        rfl

theorem cell23_7536668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_7536668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536668 prefixEnd_7536668 := by exact prefixLift 7536668
  have htrace : WordTrace (prefixWord ++ tailWord_7536668) baseStart_7536668 baseEnd_7536668 := by
    simpa [prefixWord, tailWord_7536668, baseEnd_7536668] using wordTrace_append hprefix tailTrace_7536668
  have hstable : (prefixWord ++ tailWord_7536668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536668).length < 2 ^ (prefixWord ++ tailWord_7536668).sum := by decide
  have hdescent : baseEnd_7536668 < baseStart_7536668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536698 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2]
def baseStart_7536698 : Nat := 118140960795 + 7536698 * 2 ^ 59
def prefixEnd_7536698 : Nat := 4983230072969 + 3 ^ 40 * 7536698 * 2
def baseEnd_7536698 : Nat := 3869948621779458868114363

theorem tailTrace_7536698 : CollatzResearch.WordTrace tailWord_7536698 prefixEnd_7536698 3869948621779458868114363 := by
  unfold tailWord_7536698
  simp only [CollatzResearch.WordTrace]
  refine ⟨68721489712459446596756687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183257305899891857591351165 68721489712459446596756687)
  ·
    refine ⟨103082234568689169895135031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68721489712459446596756687 103082234568689169895135031)
    ·
      refine ⟨154623351853033754842702547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103082234568689169895135031 154623351853033754842702547)
      ·
        refine ⟨231935027779550632264053821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154623351853033754842702547 231935027779550632264053821)
        ·
          refine ⟨86975635417331487099020183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231935027779550632264053821 86975635417331487099020183)
          ·
            refine ⟨130463453125997230648530275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86975635417331487099020183 130463453125997230648530275)
            ·
              refine ⟨195695179688995845972795413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130463453125997230648530275 195695179688995845972795413)
              ·
                refine ⟨9173211547921680279974785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195695179688995845972795413 9173211547921680279974785)
                ·
                  refine ⟨6879908660941260209981089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9173211547921680279974785 6879908660941260209981089)
                  ·
                    refine ⟨5159931495705945157485817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6879908660941260209981089 5159931495705945157485817)
                    ·
                      refine ⟨3869948621779458868114363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159931495705945157485817 3869948621779458868114363)
                      ·
                        rfl

theorem cell23_7536698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_7536698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536698 prefixEnd_7536698 := by exact prefixLift 7536698
  have htrace : WordTrace (prefixWord ++ tailWord_7536698) baseStart_7536698 baseEnd_7536698 := by
    simpa [prefixWord, tailWord_7536698, baseEnd_7536698] using wordTrace_append hprefix tailTrace_7536698
  have hstable : (prefixWord ++ tailWord_7536698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536698).length < 2 ^ (prefixWord ++ tailWord_7536698).sum := by decide
  have hdescent : baseEnd_7536698 < baseStart_7536698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536704 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 7]
def baseStart_7536704 : Nat := 118140960795 + 7536704 * 2 ^ 59
def prefixEnd_7536704 : Nat := 4983230072969 + 3 ^ 40 * 7536704 * 2
def baseEnd_7536704 : Nat := 429994633629265093848815

theorem tailTrace_7536704 : CollatzResearch.WordTrace tailWord_7536704 prefixEnd_7536704 429994633629265093848815 := by
  unfold tailWord_7536704
  simp only [CollatzResearch.WordTrace]
  refine ⟨137443088843908024705872583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183257451791877366274496777 137443088843908024705872583)
  ·
    refine ⟨206164633265862037058808875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137443088843908024705872583 206164633265862037058808875)
    ·
      refine ⟨309246949898793055588213313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206164633265862037058808875 309246949898793055588213313)
      ·
        refine ⟨231935212424094791691159985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309246949898793055588213313 231935212424094791691159985)
        ·
          refine ⟨173951409318071093768369989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231935212424094791691159985 173951409318071093768369989)
          ·
            refine ⟨32615889247138330081569373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173951409318071093768369989 32615889247138330081569373)
            ·
              refine ⟨12230958467676873780588515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32615889247138330081569373 12230958467676873780588515)
              ·
                refine ⟨18346437701515310670882773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12230958467676873780588515 18346437701515310670882773)
                ·
                  refine ⟨429994633629265093848815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18346437701515310670882773 429994633629265093848815)
                  ·
                    rfl

theorem cell23_7536704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 7].length) (baseStart_7536704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536704 prefixEnd_7536704 := by exact prefixLift 7536704
  have htrace : WordTrace (prefixWord ++ tailWord_7536704) baseStart_7536704 baseEnd_7536704 := by
    simpa [prefixWord, tailWord_7536704, baseEnd_7536704] using wordTrace_append hprefix tailTrace_7536704
  have hstable : (prefixWord ++ tailWord_7536704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536704).length < 2 ^ (prefixWord ++ tailWord_7536704).sum := by decide
  have hdescent : baseEnd_7536704 < baseStart_7536704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_7536707 : Nat := 118140960795 + 7536707 * 2 ^ 59
def prefixEnd_7536707 : Nat := 4983230072969 + 3 ^ 40 * 7536707 * 2
def baseEnd_7536707 : Nat := 3869953243105349332901821

theorem tailTrace_7536707 : CollatzResearch.WordTrace tailWord_7536707 prefixEnd_7536707 3869953243105349332901821 := by
  unfold tailWord_7536707
  simp only [CollatzResearch.WordTrace]
  refine ⟨274886287106805180924104375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183257524737870120616069583 274886287106805180924104375)
  ·
    refine ⟨412329430660207771386156563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274886287106805180924104375 412329430660207771386156563)
    ·
      refine ⟨618494145990311657079234845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412329430660207771386156563 618494145990311657079234845)
      ·
        refine ⟨231935304746366871404713067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618494145990311657079234845 231935304746366871404713067)
        ·
          refine ⟨347902957119550307107069601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231935304746366871404713067 347902957119550307107069601)
          ·
            refine ⟨260927217839662730330302201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347902957119550307107069601 260927217839662730330302201)
            ·
              refine ⟨195695413379747047747726651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260927217839662730330302201 195695413379747047747726651)
              ·
                refine ⟨293543120069620571621589977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195695413379747047747726651 293543120069620571621589977)
                ·
                  refine ⟨220157340052215428716192483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293543120069620571621589977 220157340052215428716192483)
                  ·
                    refine ⟨330236010078323143074288725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220157340052215428716192483 330236010078323143074288725)
                    ·
                      refine ⟨3869953243105349332901821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 330236010078323143074288725 3869953243105349332901821)
                      ·
                        rfl

theorem cell23_7536707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_7536707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536707 prefixEnd_7536707 := by exact prefixLift 7536707
  have htrace : WordTrace (prefixWord ++ tailWord_7536707) baseStart_7536707 baseEnd_7536707 := by
    simpa [prefixWord, tailWord_7536707, baseEnd_7536707] using wordTrace_append hprefix tailTrace_7536707
  have hstable : (prefixWord ++ tailWord_7536707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536707).length < 2 ^ (prefixWord ++ tailWord_7536707).sum := by decide
  have hdescent : baseEnd_7536707 < baseStart_7536707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536714 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_7536714 : Nat := 118140960795 + 7536714 * 2 ^ 59
def prefixEnd_7536714 : Nat := 4983230072969 + 3 ^ 40 * 7536714 * 2
def baseEnd_7536714 : Nat := 3869956837469930805514289

theorem tailTrace_7536714 : CollatzResearch.WordTrace tailWord_7536714 prefixEnd_7536714 3869956837469930805514289 := by
  unfold tailWord_7536714
  simp only [CollatzResearch.WordTrace]
  refine ⟨68721635604444955279902299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183257694945186547413072797 68721635604444955279902299)
  ·
    refine ⟨103082453406667432919853449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68721635604444955279902299 103082453406667432919853449)
    ·
      refine ⟨77311840055000574689890087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103082453406667432919853449 77311840055000574689890087)
      ·
        refine ⟨115967760082500862034835131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77311840055000574689890087 115967760082500862034835131)
        ·
          refine ⟨173951640123751293052252697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115967760082500862034835131 173951640123751293052252697)
          ·
            refine ⟨130463730092813469789189523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173951640123751293052252697 130463730092813469789189523)
            ·
              refine ⟨195695595139220204683784285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130463730092813469789189523 195695595139220204683784285)
              ·
                refine ⟨73385848177207576756419107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195695595139220204683784285 73385848177207576756419107)
                ·
                  refine ⟨110078772265811365134628661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73385848177207576756419107 110078772265811365134628661)
                  ·
                    refine ⟨10319884899919815481371437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110078772265811365134628661 10319884899919815481371437)
                    ·
                      refine ⟨3869956837469930805514289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10319884899919815481371437 3869956837469930805514289)
                      ·
                        rfl

theorem cell23_7536714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_7536714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536714 prefixEnd_7536714 := by exact prefixLift 7536714
  have htrace : WordTrace (prefixWord ++ tailWord_7536714) baseStart_7536714 baseEnd_7536714 := by
    simpa [prefixWord, tailWord_7536714, baseEnd_7536714] using wordTrace_append hprefix tailTrace_7536714
  have hstable : (prefixWord ++ tailWord_7536714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536714).length < 2 ^ (prefixWord ++ tailWord_7536714).sum := by decide
  have hdescent : baseEnd_7536714 < baseStart_7536714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536758 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7536758 : Nat := 118140960795 + 7536758 * 2 ^ 59
def prefixEnd_7536758 : Nat := 4983230072969 + 3 ^ 40 * 7536758 * 2
def baseEnd_7536758 : Nat := 3869979430618728633364087

theorem tailTrace_7536758 : CollatzResearch.WordTrace tailWord_7536758 prefixEnd_7536758 3869979430618728633364087 := by
  unfold tailWord_7536758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17180509201851276039638183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183258764819746944422807285 17180509201851276039638183)
  ·
    refine ⟨25770763802776914059457275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17180509201851276039638183 25770763802776914059457275)
    ·
      refine ⟨38656145704165371089185913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25770763802776914059457275 38656145704165371089185913)
      ·
        refine ⟨28992109278124028316889435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38656145704165371089185913 28992109278124028316889435)
        ·
          refine ⟨43488163917186042475334153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28992109278124028316889435 43488163917186042475334153)
          ·
            refine ⟨32616122937889531856500615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43488163917186042475334153 32616122937889531856500615)
            ·
              refine ⟨48924184406834297784750923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32616122937889531856500615 48924184406834297784750923)
              ·
                refine ⟨73386276610251446677126385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48924184406834297784750923 73386276610251446677126385)
                ·
                  refine ⟨55039707457688585007844789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73386276610251446677126385 55039707457688585007844789)
                  ·
                    refine ⟨5159972574158304844485449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55039707457688585007844789 5159972574158304844485449)
                    ·
                      refine ⟨3869979430618728633364087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159972574158304844485449 3869979430618728633364087)
                      ·
                        rfl

theorem cell23_7536758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7536758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536758 prefixEnd_7536758 := by exact prefixLift 7536758
  have htrace : WordTrace (prefixWord ++ tailWord_7536758) baseStart_7536758 baseEnd_7536758 := by
    simpa [prefixWord, tailWord_7536758, baseEnd_7536758] using wordTrace_append hprefix tailTrace_7536758
  have hstable : (prefixWord ++ tailWord_7536758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536758).length < 2 ^ (prefixWord ++ tailWord_7536758).sum := by decide
  have hdescent : baseEnd_7536758 < baseStart_7536758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536771 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 6, 2]
def baseStart_7536771 : Nat := 118140960795 + 7536771 * 2 ^ 59
def prefixEnd_7536771 : Nat := 4983230072969 + 3 ^ 40 * 7536771 * 2
def baseEnd_7536771 : Nat := 3869986105867237082501527

theorem tailTrace_7536771 : CollatzResearch.WordTrace tailWord_7536771 prefixEnd_7536771 3869986105867237082501527 := by
  unfold tailWord_7536771
  simp only [CollatzResearch.WordTrace]
  refine ⟨274888621378573319854434167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183259080919048879902956111 274888621378573319854434167)
  ·
    refine ⟨412332932067859979781651251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274888621378573319854434167 412332932067859979781651251)
    ·
      refine ⟨618499398101789969672476877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412332932067859979781651251 618499398101789969672476877)
      ·
        refine ⟨231937274288171238627178829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618499398101789969672476877 231937274288171238627178829)
        ·
          refine ⟨86976477858064214485192061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231937274288171238627178829 86976477858064214485192061)
          ·
            refine ⟨32616179196774080431947023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86976477858064214485192061 32616179196774080431947023)
            ·
              refine ⟨48924268795161120647920535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32616179196774080431947023 48924268795161120647920535)
              ·
                refine ⟨73386403192741680971880803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48924268795161120647920535 73386403192741680971880803)
                ·
                  refine ⟨110079604789112521457821205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73386403192741680971880803 110079604789112521457821205)
                  ·
                    refine ⟨5159981474489649443335369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110079604789112521457821205 5159981474489649443335369)
                    ·
                      refine ⟨3869986105867237082501527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5159981474489649443335369 3869986105867237082501527)
                      ·
                        rfl

theorem cell23_7536771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_7536771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536771 prefixEnd_7536771 := by exact prefixLift 7536771
  have htrace : WordTrace (prefixWord ++ tailWord_7536771) baseStart_7536771 baseEnd_7536771 := by
    simpa [prefixWord, tailWord_7536771, baseEnd_7536771] using wordTrace_append hprefix tailTrace_7536771
  have hstable : (prefixWord ++ tailWord_7536771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536771).length < 2 ^ (prefixWord ++ tailWord_7536771).sum := by decide
  have hdescent : baseEnd_7536771 < baseStart_7536771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536866 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7536866 : Nat := 118140960795 + 7536866 * 2 ^ 59
def prefixEnd_7536866 : Nat := 4983230072969 + 3 ^ 40 * 7536866 * 2
def baseEnd_7536866 : Nat := 1290011628843138070271197

theorem tailTrace_7536866 : CollatzResearch.WordTrace tailWord_7536866 prefixEnd_7536866 1290011628843138070271197 := by
  unfold tailWord_7536866
  simp only [CollatzResearch.WordTrace]
  refine ⟨68723021578307287769785613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183261390875486100719428301 68723021578307287769785613)
  ·
    refine ⟨25771133091865232913669605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68723021578307287769785613 25771133091865232913669605)
    ·
      refine ⟨4832087454724731171313051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25771133091865232913669605 4832087454724731171313051)
      ·
        refine ⟨7248131182087096756969577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832087454724731171313051 7248131182087096756969577)
        ·
          refine ⟨5436098386565322567727183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248131182087096756969577 5436098386565322567727183)
          ·
            refine ⟨8154147579847983851590775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436098386565322567727183 8154147579847983851590775)
            ·
              refine ⟨12231221369771975777386163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8154147579847983851590775 12231221369771975777386163)
              ·
                refine ⟨18346832054657963666079245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231221369771975777386163 18346832054657963666079245)
                ·
                  refine ⟨6880062020496736374779717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18346832054657963666079245 6880062020496736374779717)
                  ·
                    refine ⟨1290011628843138070271197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880062020496736374779717 1290011628843138070271197)
                    ·
                      rfl

theorem cell23_7536866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7536866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536866 prefixEnd_7536866 := by exact prefixLift 7536866
  have htrace : WordTrace (prefixWord ++ tailWord_7536866) baseStart_7536866 baseEnd_7536866 := by
    simpa [prefixWord, tailWord_7536866, baseEnd_7536866] using wordTrace_append hprefix tailTrace_7536866
  have hstable : (prefixWord ++ tailWord_7536866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536866).length < 2 ^ (prefixWord ++ tailWord_7536866).sum := by decide
  have hdescent : baseEnd_7536866 < baseStart_7536866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536881 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_7536881 : Nat := 118140960795 + 7536881 * 2 ^ 59
def prefixEnd_7536881 : Nat := 4983230072969 + 3 ^ 40 * 7536881 * 2
def baseEnd_7536881 : Nat := 3870042588739231652126021

theorem tailTrace_7536881 : CollatzResearch.WordTrace tailWord_7536881 prefixEnd_7536881 3870042588739231652126021 := by
  unfold tailWord_7536881
  simp only [CollatzResearch.WordTrace]
  refine ⟨274892633408174808640938497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183261755605449872427292331 274892633408174808640938497)
  ·
    refine ⟨206169475056131106480703873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274892633408174808640938497 206169475056131106480703873)
    ·
      refine ⟨154627106292098329860527905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206169475056131106480703873 154627106292098329860527905)
      ·
        refine ⟨115970329719073747395395929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154627106292098329860527905 115970329719073747395395929)
        ·
          refine ⟨86977747289305310546546947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115970329719073747395395929 86977747289305310546546947)
          ·
            refine ⟨130466620933957965819820421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86977747289305310546546947 130466620933957965819820421)
            ·
              refine ⟨24462491425117118591216329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130466620933957965819820421 24462491425117118591216329)
              ·
                refine ⟨18346868568837838943412247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24462491425117118591216329 18346868568837838943412247)
                ·
                  refine ⟨27520302853256758415118371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18346868568837838943412247 27520302853256758415118371)
                  ·
                    refine ⟨41280454279885137622677557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27520302853256758415118371 41280454279885137622677557)
                    ·
                      refine ⟨3870042588739231652126021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41280454279885137622677557 3870042588739231652126021)
                      ·
                        rfl

theorem cell23_7536881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_7536881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536881 prefixEnd_7536881 := by exact prefixLift 7536881
  have htrace : WordTrace (prefixWord ++ tailWord_7536881) baseStart_7536881 baseEnd_7536881 := by
    simpa [prefixWord, tailWord_7536881, baseEnd_7536881] using wordTrace_append hprefix tailTrace_7536881
  have hstable : (prefixWord ++ tailWord_7536881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536881).length < 2 ^ (prefixWord ++ tailWord_7536881).sum := by decide
  have hdescent : baseEnd_7536881 < baseStart_7536881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536929 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7536929 : Nat := 118140960795 + 7536929 * 2 ^ 59
def prefixEnd_7536929 : Nat := 4983230072969 + 3 ^ 40 * 7536929 * 2
def baseEnd_7536929 : Nat := 3870067235810647464325801

theorem tailTrace_7536929 : CollatzResearch.WordTrace tailWord_7536929 prefixEnd_7536929 3870067235810647464325801 := by
  unfold tailWord_7536929
  simp only [CollatzResearch.WordTrace]
  refine ⟨274894384112000912838685841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183262922741333941892457227 274894384112000912838685841)
  ·
    refine ⟨206170788084000684629014381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274894384112000912838685841 206170788084000684629014381)
    ·
      refine ⟨77314045531500256735880393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206170788084000684629014381 77314045531500256735880393)
      ·
        refine ⟨57985534148625192551910295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77314045531500256735880393 57985534148625192551910295)
        ·
          refine ⟨86978301222937788827865443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57985534148625192551910295 86978301222937788827865443)
          ·
            refine ⟨130467451834406683241798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86978301222937788827865443 130467451834406683241798165)
            ·
              refine ⟨6115661804737813276959289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130467451834406683241798165 6115661804737813276959289)
              ·
                refine ⟨4586746353553359957719467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115661804737813276959289 4586746353553359957719467)
                ·
                  refine ⟨6880119530330039936579201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586746353553359957719467 6880119530330039936579201)
                  ·
                    refine ⟨5160089647747529952434401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6880119530330039936579201 5160089647747529952434401)
                    ·
                      refine ⟨3870067235810647464325801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160089647747529952434401 3870067235810647464325801)
                      ·
                        rfl

theorem cell23_7536929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7536929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536929 prefixEnd_7536929 := by exact prefixLift 7536929
  have htrace : WordTrace (prefixWord ++ tailWord_7536929) baseStart_7536929 baseEnd_7536929 := by
    simpa [prefixWord, tailWord_7536929, baseEnd_7536929] using wordTrace_append hprefix tailTrace_7536929
  have hstable : (prefixWord ++ tailWord_7536929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536929).length < 2 ^ (prefixWord ++ tailWord_7536929).sum := by decide
  have hdescent : baseEnd_7536929 < baseStart_7536929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536942 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7536942 : Nat := 118140960795 + 7536942 * 2 ^ 59
def prefixEnd_7536942 : Nat := 4983230072969 + 3 ^ 40 * 7536942 * 2
def baseEnd_7536942 : Nat := 3870073911059155913463241

theorem tailTrace_7536942 : CollatzResearch.WordTrace tailWord_7536942 prefixEnd_7536942 3870073911059155913463241 := by
  unfold tailWord_7536942
  simp only [CollatzResearch.WordTrace]
  refine ⟨34361857282619227007363635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183263238840635877372606053 34361857282619227007363635)
  ·
    refine ⟨51542785923928840511045453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34361857282619227007363635 51542785923928840511045453)
    ·
      refine ⟨19328544721473315191642045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51542785923928840511045453 19328544721473315191642045)
      ·
        refine ⟨7248204270552493196865767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19328544721473315191642045 7248204270552493196865767)
        ·
          refine ⟨10872306405828739795298651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248204270552493196865767 10872306405828739795298651)
          ·
            refine ⟨16308459608743109692947977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872306405828739795298651 16308459608743109692947977)
            ·
              refine ⟨12231344706557332269710983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16308459608743109692947977 12231344706557332269710983)
              ·
                refine ⟨18347017059835998404566475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231344706557332269710983 18347017059835998404566475)
                ·
                  refine ⟨27520525589753997606849713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18347017059835998404566475 27520525589753997606849713)
                  ·
                    refine ⟨20640394192315498205137285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27520525589753997606849713 20640394192315498205137285)
                    ·
                      refine ⟨3870073911059155913463241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20640394192315498205137285 3870073911059155913463241)
                      ·
                        rfl

theorem cell23_7536942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7536942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536942 prefixEnd_7536942 := by exact prefixLift 7536942
  have htrace : WordTrace (prefixWord ++ tailWord_7536942) baseStart_7536942 baseEnd_7536942 := by
    simpa [prefixWord, tailWord_7536942, baseEnd_7536942] using wordTrace_append hprefix tailTrace_7536942
  have hstable : (prefixWord ++ tailWord_7536942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536942).length < 2 ^ (prefixWord ++ tailWord_7536942).sum := by decide
  have hdescent : baseEnd_7536942 < baseStart_7536942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536945 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_7536945 : Nat := 118140960795 + 7536945 * 2 ^ 59
def prefixEnd_7536945 : Nat := 4983230072969 + 3 ^ 40 * 7536945 * 2
def baseEnd_7536945 : Nat := 3870075451501119401725727

theorem tailTrace_7536945 : CollatzResearch.WordTrace tailWord_7536945 prefixEnd_7536945 3870075451501119401725727 := by
  unfold tailWord_7536945
  simp only [CollatzResearch.WordTrace]
  refine ⟨274894967679942947571268289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183263311786628631714178859 274894967679942947571268289)
  ·
    refine ⟨206171225759957210678451217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274894967679942947571268289 206171225759957210678451217)
    ·
      refine ⟨154628419319967908008838413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206171225759957210678451217 154628419319967908008838413)
      ·
        refine ⟨57985657244987965503314405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154628419319967908008838413 57985657244987965503314405)
        ·
          refine ⟨10872310733435243531871451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57985657244987965503314405 10872310733435243531871451)
          ·
            refine ⟨16308466100152865297807177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872310733435243531871451 16308466100152865297807177)
            ·
              refine ⟨12231349575114648973355383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16308466100152865297807177 12231349575114648973355383)
              ·
                refine ⟨18347024362671973460033075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231349575114648973355383 18347024362671973460033075)
                ·
                  refine ⟨27520536544007960190049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18347024362671973460033075 27520536544007960190049613)
                  ·
                    refine ⟨10320201204002985071268605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27520536544007960190049613 10320201204002985071268605)
                    ·
                      refine ⟨3870075451501119401725727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320201204002985071268605 3870075451501119401725727)
                      ·
                        rfl

theorem cell23_7536945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_7536945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536945 prefixEnd_7536945 := by exact prefixLift 7536945
  have htrace : WordTrace (prefixWord ++ tailWord_7536945) baseStart_7536945 baseEnd_7536945 := by
    simpa [prefixWord, tailWord_7536945, baseEnd_7536945] using wordTrace_append hprefix tailTrace_7536945
  have hstable : (prefixWord ++ tailWord_7536945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536945).length < 2 ^ (prefixWord ++ tailWord_7536945).sum := by decide
  have hdescent : baseEnd_7536945 < baseStart_7536945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3]
def baseStart_7536971 : Nat := 118140960795 + 7536971 * 2 ^ 59
def prefixEnd_7536971 : Nat := 4983230072969 + 3 ^ 40 * 7536971 * 2
def baseEnd_7536971 : Nat := 3870088801998136300000607

theorem tailTrace_7536971 : CollatzResearch.WordTrace tailWord_7536971 prefixEnd_7536971 3870088801998136300000607 := by
  unfold tailWord_7536971
  simp only [CollatzResearch.WordTrace]
  refine ⟨274895915977848754011714767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183263943985232502674476511 274895915977848754011714767)
  ·
    refine ⟨412343873966773131017572151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274895915977848754011714767 412343873966773131017572151)
    ·
      refine ⟨618515810950159696526358227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412343873966773131017572151 618515810950159696526358227)
      ·
        refine ⟨927773716425239544789537341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618515810950159696526358227 927773716425239544789537341)
        ·
          refine ⟨347915143659464829296076503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927773716425239544789537341 347915143659464829296076503)
          ·
            refine ⟨521872715489197243944114755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347915143659464829296076503 521872715489197243944114755)
            ·
              refine ⟨782809073233795865916172133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521872715489197243944114755 782809073233795865916172133)
              ·
                refine ⟨146776701231336724859282275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782809073233795865916172133 146776701231336724859282275)
                ·
                  refine ⟨220165051847005087288923413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146776701231336724859282275 220165051847005087288923413)
                  ·
                    refine ⟨10320236805328363466668285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 220165051847005087288923413 10320236805328363466668285)
                    ·
                      refine ⟨3870088801998136300000607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320236805328363466668285 3870088801998136300000607)
                      ·
                        rfl

theorem cell23_7536971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 3].length) (baseStart_7536971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536971 prefixEnd_7536971 := by exact prefixLift 7536971
  have htrace : WordTrace (prefixWord ++ tailWord_7536971) baseStart_7536971 baseEnd_7536971 := by
    simpa [prefixWord, tailWord_7536971, baseEnd_7536971] using wordTrace_append hprefix tailTrace_7536971
  have hstable : (prefixWord ++ tailWord_7536971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536971).length < 2 ^ (prefixWord ++ tailWord_7536971).sum := by decide
  have hdescent : baseEnd_7536971 < baseStart_7536971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7536991 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 7]
def baseStart_7536991 : Nat := 118140960795 + 7536991 * 2 ^ 59
def prefixEnd_7536991 : Nat := 4983230072969 + 3 ^ 40 * 7536991 * 2
def baseEnd_7536991 : Nat := 430011007956802913527835

theorem tailTrace_7536991 : CollatzResearch.WordTrace tailWord_7536991 prefixEnd_7536991 430011007956802913527835 := by
  unfold tailWord_7536991
  simp only [CollatzResearch.WordTrace]
  refine ⟨274896645437776297427442827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183264430291850864951628551 274896645437776297427442827)
  ·
    refine ⟨412344968156664446141164241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274896645437776297427442827 412344968156664446141164241)
    ·
      refine ⟨309258726117498334605873181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412344968156664446141164241 309258726117498334605873181)
      ·
        refine ⟨115972022294061875477202443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309258726117498334605873181 115972022294061875477202443)
        ·
          refine ⟨173958033441092813215803665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115972022294061875477202443 173958033441092813215803665)
          ·
            refine ⟨130468525080819609911852749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173958033441092813215803665 130468525080819609911852749)
            ·
              refine ⟨48925696905307353716944781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130468525080819609911852749 48925696905307353716944781)
              ·
                refine ⟨18347136339490257643854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48925696905307353716944781 18347136339490257643854293)
                ·
                  refine ⟨430011007956802913527835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18347136339490257643854293 430011007956802913527835)
                  ·
                    rfl

theorem cell23_7536991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 7].length) (baseStart_7536991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7536991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7536991 prefixEnd_7536991 := by exact prefixLift 7536991
  have htrace : WordTrace (prefixWord ++ tailWord_7536991) baseStart_7536991 baseEnd_7536991 := by
    simpa [prefixWord, tailWord_7536991, baseEnd_7536991] using wordTrace_append hprefix tailTrace_7536991
  have hstable : (prefixWord ++ tailWord_7536991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7536991).length < 2 ^ (prefixWord ++ tailWord_7536991).sum := by decide
  have hdescent : baseEnd_7536991 < baseStart_7536991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7536991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537002 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7537002 : Nat := 118140960795 + 7537002 * 2 ^ 59
def prefixEnd_7537002 : Nat := 4983230072969 + 3 ^ 40 * 7537002 * 2
def baseEnd_7537002 : Nat := 3870104719898425678712965

theorem tailTrace_7537002 : CollatzResearch.WordTrace tailWord_7537002 prefixEnd_7537002 3870104719898425678712965 := by
  unfold tailWord_7537002
  simp only [CollatzResearch.WordTrace]
  refine ⟨68724261660184111576523315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183264697760490964204062173 68724261660184111576523315)
  ·
    refine ⟨103086392490276167364784973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68724261660184111576523315 103086392490276167364784973)
    ·
      refine ⟨38657397183853562761794365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103086392490276167364784973 38657397183853562761794365)
      ·
        refine ⟨14496523943945086035672887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38657397183853562761794365 14496523943945086035672887)
        ·
          refine ⟨21744785915917629053509331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496523943945086035672887 21744785915917629053509331)
          ·
            refine ⟨32617178873876443580263997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744785915917629053509331 32617178873876443580263997)
            ·
              refine ⟨12231442077703666342598999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32617178873876443580263997 12231442077703666342598999)
              ·
                refine ⟨18347163116555499513898499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231442077703666342598999 18347163116555499513898499)
                ·
                  refine ⟨27520744674833249270847749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18347163116555499513898499 27520744674833249270847749)
                  ·
                    refine ⟨5160139626531234238283953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27520744674833249270847749 5160139626531234238283953)
                    ·
                      refine ⟨3870104719898425678712965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160139626531234238283953 3870104719898425678712965)
                      ·
                        rfl

theorem cell23_7537002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7537002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537002 prefixEnd_7537002 := by exact prefixLift 7537002
  have htrace : WordTrace (prefixWord ++ tailWord_7537002) baseStart_7537002 baseEnd_7537002 := by
    simpa [prefixWord, tailWord_7537002, baseEnd_7537002] using wordTrace_append hprefix tailTrace_7537002
  have hstable : (prefixWord ++ tailWord_7537002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537002).length < 2 ^ (prefixWord ++ tailWord_7537002).sum := by decide
  have hdescent : baseEnd_7537002 < baseStart_7537002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537048 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7537048 : Nat := 118140960795 + 7537048 * 2 ^ 59
def prefixEnd_7537048 : Nat := 4983230072969 + 3 ^ 40 * 7537048 * 2
def baseEnd_7537048 : Nat := 3870128340008532498737753

theorem tailTrace_7537048 : CollatzResearch.WordTrace tailWord_7537048 prefixEnd_7537048 3870128340008532498737753 := by
  unfold tailWord_7537048
  simp only [CollatzResearch.WordTrace]
  refine ⟨137449362199284898081133899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183265816265713197441511865 137449362199284898081133899)
  ·
    refine ⟨206174043298927347121700849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137449362199284898081133899 206174043298927347121700849)
    ·
      refine ⟨154630532474195510341275637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206174043298927347121700849 154630532474195510341275637)
      ·
        refine ⟨14496612419455829094494591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154630532474195510341275637 14496612419455829094494591)
        ·
          refine ⟨21744918629183743641741887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496612419455829094494591 21744918629183743641741887)
          ·
            refine ⟨32617377943775615462612831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744918629183743641741887 32617377943775615462612831)
            ·
              refine ⟨48926066915663423193919247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32617377943775615462612831 48926066915663423193919247)
              ·
                refine ⟨73389100373495134790878871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48926066915663423193919247 73389100373495134790878871)
                ·
                  refine ⟨110083650560242702186318307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73389100373495134790878871 110083650560242702186318307)
                  ·
                    refine ⟨165125475840364053279477461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110083650560242702186318307 165125475840364053279477461)
                    ·
                      refine ⟨3870128340008532498737753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165125475840364053279477461 3870128340008532498737753)
                      ·
                        rfl

theorem cell23_7537048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7537048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537048 prefixEnd_7537048 := by exact prefixLift 7537048
  have htrace : WordTrace (prefixWord ++ tailWord_7537048) baseStart_7537048 baseEnd_7537048 := by
    simpa [prefixWord, tailWord_7537048, baseEnd_7537048] using wordTrace_append hprefix tailTrace_7537048
  have hstable : (prefixWord ++ tailWord_7537048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537048).length < 2 ^ (prefixWord ++ tailWord_7537048).sum := by decide
  have hdescent : baseEnd_7537048 < baseStart_7537048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537053 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_7537053 : Nat := 118140960795 + 7537053 * 2 ^ 59
def prefixEnd_7537053 : Nat := 4983230072969 + 3 ^ 40 * 7537053 * 2
def baseEnd_7537053 : Nat := 3870130907411804979175231

theorem tailTrace_7537053 : CollatzResearch.WordTrace tailWord_7537053 prefixEnd_7537053 3870130907411804979175231 := by
  unfold tailWord_7537053
  simp only [CollatzResearch.WordTrace]
  refine ⟨274898906763551682016199813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183265937842367788010799875 274898906763551682016199813)
  ·
    refine ⟨51543545018165940378037465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274898906763551682016199813 51543545018165940378037465)
    ·
      refine ⟨38657658763624455283528099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51543545018165940378037465 38657658763624455283528099)
      ·
        refine ⟨57986488145436682925292149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38657658763624455283528099 57986488145436682925292149)
        ·
          refine ⟨5436233263634689024246139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57986488145436682925292149 5436233263634689024246139)
          ·
            refine ⟨8154349895452033536369209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436233263634689024246139 8154349895452033536369209)
            ·
              refine ⟨6115762421589025152276907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8154349895452033536369209 6115762421589025152276907)
              ·
                refine ⟨9173643632383537728415361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115762421589025152276907 9173643632383537728415361)
                ·
                  refine ⟨6880232724287653296311521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9173643632383537728415361 6880232724287653296311521)
                  ·
                    refine ⟨5160174543215739972233641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6880232724287653296311521 5160174543215739972233641)
                    ·
                      refine ⟨3870130907411804979175231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160174543215739972233641 3870130907411804979175231)
                      ·
                        rfl

theorem cell23_7537053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_7537053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537053 prefixEnd_7537053 := by exact prefixLift 7537053
  have htrace : WordTrace (prefixWord ++ tailWord_7537053) baseStart_7537053 baseEnd_7537053 := by
    simpa [prefixWord, tailWord_7537053, baseEnd_7537053] using wordTrace_append hprefix tailTrace_7537053
  have hstable : (prefixWord ++ tailWord_7537053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537053).length < 2 ^ (prefixWord ++ tailWord_7537053).sum := by decide
  have hdescent : baseEnd_7537053 < baseStart_7537053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537068 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_7537068 : Nat := 118140960795 + 7537068 * 2 ^ 59
def prefixEnd_7537068 : Nat := 4983230072969 + 3 ^ 40 * 7537068 * 2
def baseEnd_7537068 : Nat := 1290046203207207473495887

theorem tailTrace_7537068 : CollatzResearch.WordTrace tailWord_7537068 prefixEnd_7537068 1290046203207207473495887 := by
  unfold tailWord_7537068
  simp only [CollatzResearch.WordTrace]
  refine ⟨137449726929248669788997929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183266302572331559718663905 137449726929248669788997929)
  ·
    refine ⟨103087295196936502341748447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137449726929248669788997929 103087295196936502341748447)
    ·
      refine ⟨154630942795404753512622671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103087295196936502341748447 154630942795404753512622671)
      ·
        refine ⟨231946414193107130268934007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154630942795404753512622671 231946414193107130268934007)
        ·
          refine ⟨347919621289660695403401011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231946414193107130268934007 347919621289660695403401011)
          ·
            refine ⟨521879431934491043105101517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347919621289660695403401011 521879431934491043105101517)
            ·
              refine ⟨195704786975434141164413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521879431934491043105101517 195704786975434141164413069)
              ·
                refine ⟨73389295115787802936654901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195704786975434141164413069 73389295115787802936654901)
                ·
                  refine ⟨6880246417105106525311397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73389295115787802936654901 6880246417105106525311397)
                  ·
                    refine ⟨1290046203207207473495887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880246417105106525311397 1290046203207207473495887)
                    ·
                      rfl

theorem cell23_7537068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_7537068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537068 prefixEnd_7537068 := by exact prefixLift 7537068
  have htrace : WordTrace (prefixWord ++ tailWord_7537068) baseStart_7537068 baseEnd_7537068 := by
    simpa [prefixWord, tailWord_7537068, baseEnd_7537068] using wordTrace_append hprefix tailTrace_7537068
  have hstable : (prefixWord ++ tailWord_7537068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537068).length < 2 ^ (prefixWord ++ tailWord_7537068).sum := by decide
  have hdescent : baseEnd_7537068 < baseStart_7537068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537071 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_7537071 : Nat := 118140960795 + 7537071 * 2 ^ 59
def prefixEnd_7537071 : Nat := 4983230072969 + 3 ^ 40 * 7537071 * 2
def baseEnd_7537071 : Nat := 3870140150063585908750147

theorem tailTrace_7537071 : CollatzResearch.WordTrace tailWord_7537071 prefixEnd_7537071 3870140150063585908750147 := by
  unfold tailWord_7537071
  simp only [CollatzResearch.WordTrace]
  refine ⟨274899563277486471090355067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183266375518324314060236711 274899563277486471090355067)
  ·
    refine ⟨412349344916229706635532601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274899563277486471090355067 412349344916229706635532601)
    ·
      refine ⟨309262008687172279976649451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412349344916229706635532601 309262008687172279976649451)
      ·
        refine ⟨463893013030758419964974177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309262008687172279976649451 463893013030758419964974177)
        ·
          refine ⟨347919759773068814973730633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463893013030758419964974177 347919759773068814973730633)
          ·
            refine ⟨260939819829801611230297975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347919759773068814973730633 260939819829801611230297975)
            ·
              refine ⟨391409729744702416845446963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260939819829801611230297975 391409729744702416845446963)
              ·
                refine ⟨587114594617053625268170445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391409729744702416845446963 587114594617053625268170445)
                ·
                  refine ⟨220167972981395109475563917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 587114594617053625268170445 220167972981395109475563917)
                  ·
                    refine ⟨82562989868023166053336469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220167972981395109475563917 82562989868023166053336469)
                    ·
                      refine ⟨3870140150063585908750147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82562989868023166053336469 3870140150063585908750147)
                      ·
                        rfl

theorem cell23_7537071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_7537071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537071 prefixEnd_7537071 := by exact prefixLift 7537071
  have htrace : WordTrace (prefixWord ++ tailWord_7537071) baseStart_7537071 baseEnd_7537071 := by
    simpa [prefixWord, tailWord_7537071, baseEnd_7537071] using wordTrace_append hprefix tailTrace_7537071
  have hstable : (prefixWord ++ tailWord_7537071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537071).length < 2 ^ (prefixWord ++ tailWord_7537071).sum := by decide
  have hdescent : baseEnd_7537071 < baseStart_7537071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537095 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_7537095 : Nat := 118140960795 + 7537095 * 2 ^ 59
def prefixEnd_7537095 : Nat := 4983230072969 + 3 ^ 40 * 7537095 * 2
def baseEnd_7537095 : Nat := 3870152473599293814850037

theorem tailTrace_7537095 : CollatzResearch.WordTrace tailWord_7537095 prefixEnd_7537095 3870152473599293814850037 := by
  unfold tailWord_7537095
  simp only [CollatzResearch.WordTrace]
  refine ⟨274900438629399523189228739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183266959086266348792819159 274900438629399523189228739)
  ·
    refine ⟨412350657944099284783843109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274900438629399523189228739 412350657944099284783843109)
    ·
      refine ⟨77315748364518615896970583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412350657944099284783843109 77315748364518615896970583)
      ·
        refine ⟨115973622546777923845455875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77315748364518615896970583 115973622546777923845455875)
        ·
          refine ⟨173960433820166885768183813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115973622546777923845455875 173960433820166885768183813)
          ·
            refine ⟨32617581341281291081534465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173960433820166885768183813 32617581341281291081534465)
            ·
              refine ⟨24463186005960968311150849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32617581341281291081534465 24463186005960968311150849)
              ·
                refine ⟨18347389504470726233363137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24463186005960968311150849 18347389504470726233363137)
                ·
                  refine ⟨13760542128353044675022353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18347389504470726233363137 13760542128353044675022353)
                  ·
                    refine ⟨10320406596264783506266765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13760542128353044675022353 10320406596264783506266765)
                    ·
                      refine ⟨3870152473599293814850037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320406596264783506266765 3870152473599293814850037)
                      ·
                        rfl

theorem cell23_7537095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_7537095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537095 prefixEnd_7537095 := by exact prefixLift 7537095
  have htrace : WordTrace (prefixWord ++ tailWord_7537095) baseStart_7537095 baseEnd_7537095 := by
    simpa [prefixWord, tailWord_7537095, baseEnd_7537095] using wordTrace_append hprefix tailTrace_7537095
  have hstable : (prefixWord ++ tailWord_7537095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537095).length < 2 ^ (prefixWord ++ tailWord_7537095).sum := by decide
  have hdescent : baseEnd_7537095 < baseStart_7537095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537142 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7537142 : Nat := 118140960795 + 7537142 * 2 ^ 59
def prefixEnd_7537142 : Nat := 4983230072969 + 3 ^ 40 * 7537142 * 2
def baseEnd_7537142 : Nat := 3870176607190055130962321

theorem tailTrace_7537142 : CollatzResearch.WordTrace tailWord_7537142 prefixEnd_7537142 3870176607190055130962321 := by
  unfold tailWord_7537142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181384553764328138511855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183268101906819500144126453 17181384553764328138511855)
  ·
    refine ⟨25772076830646492207767783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17181384553764328138511855 25772076830646492207767783)
    ·
      refine ⟨38658115245969738311651675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25772076830646492207767783 38658115245969738311651675)
      ·
        refine ⟨57987172868954607467477513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38658115245969738311651675 57987172868954607467477513)
        ·
          refine ⟨43490379651715955600608135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57987172868954607467477513 43490379651715955600608135)
          ·
            refine ⟨65235569477573933400912203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43490379651715955600608135 65235569477573933400912203)
            ·
              refine ⟨97853354216360900101368305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65235569477573933400912203 97853354216360900101368305)
              ·
                refine ⟨73390015662270675076026229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97853354216360900101368305 73390015662270675076026229)
                ·
                  refine ⟨6880313968337875788377459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73390015662270675076026229 6880313968337875788377459)
                  ·
                    refine ⟨10320470952506813682566189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880313968337875788377459 10320470952506813682566189)
                    ·
                      refine ⟨3870176607190055130962321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320470952506813682566189 3870176607190055130962321)
                      ·
                        rfl

theorem cell23_7537142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7537142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537142 prefixEnd_7537142 := by exact prefixLift 7537142
  have htrace : WordTrace (prefixWord ++ tailWord_7537142) baseStart_7537142 baseEnd_7537142 := by
    simpa [prefixWord, tailWord_7537142, baseEnd_7537142] using wordTrace_append hprefix tailTrace_7537142
  have hstable : (prefixWord ++ tailWord_7537142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537142).length < 2 ^ (prefixWord ++ tailWord_7537142).sum := by decide
  have hdescent : baseEnd_7537142 < baseStart_7537142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537159 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7537159 : Nat := 118140960795 + 7537159 * 2 ^ 59
def prefixEnd_7537159 : Nat := 4983230072969 + 3 ^ 40 * 7537159 * 2
def baseEnd_7537159 : Nat := 3870185336361181564449743

theorem tailTrace_7537159 : CollatzResearch.WordTrace tailWord_7537159 prefixEnd_7537159 3870185336361181564449743 := by
  unfold tailWord_7537159
  simp only [CollatzResearch.WordTrace]
  refine ⟨274902772901167662119558531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183268515267445108079705687 274902772901167662119558531)
  ·
    refine ⟨412354159351751493179337797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274902772901167662119558531 412354159351751493179337797)
    ·
      refine ⟨77316404878453404971125837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412354159351751493179337797 77316404878453404971125837)
      ·
        refine ⟨28993651829420026864172189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77316404878453404971125837 28993651829420026864172189)
        ·
          refine ⟨10872619436032510074064571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28993651829420026864172189 10872619436032510074064571)
          ·
            refine ⟨16308929154048765111096857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872619436032510074064571 16308929154048765111096857)
            ·
              refine ⟨12231696865536573833322643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16308929154048765111096857 12231696865536573833322643)
              ·
                refine ⟨18347545298304860749983965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231696865536573833322643 18347545298304860749983965)
                ·
                  refine ⟨6880329486864322781243987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18347545298304860749983965 6880329486864322781243987)
                  ·
                    refine ⟨10320494230296484171865981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880329486864322781243987 10320494230296484171865981)
                    ·
                      refine ⟨3870185336361181564449743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320494230296484171865981 3870185336361181564449743)
                      ·
                        rfl

theorem cell23_7537159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7537159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537159 prefixEnd_7537159 := by exact prefixLift 7537159
  have htrace : WordTrace (prefixWord ++ tailWord_7537159) baseStart_7537159 baseEnd_7537159 := by
    simpa [prefixWord, tailWord_7537159, baseEnd_7537159] using wordTrace_append hprefix tailTrace_7537159
  have hstable : (prefixWord ++ tailWord_7537159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537159).length < 2 ^ (prefixWord ++ tailWord_7537159).sum := by decide
  have hdescent : baseEnd_7537159 < baseStart_7537159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537192 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_7537192 : Nat := 118140960795 + 7537192 * 2 ^ 59
def prefixEnd_7537192 : Nat := 4983230072969 + 3 ^ 40 * 7537192 * 2
def baseEnd_7537192 : Nat := 1290067427074259978445697

theorem tailTrace_7537192 : CollatzResearch.WordTrace tailWord_7537192 prefixEnd_7537192 1290067427074259978445697 := by
  unfold tailWord_7537192
  simp only [CollatzResearch.WordTrace]
  refine ⟨137451988255024054377754915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183269317673365405837006553 137451988255024054377754915)
  ·
    refine ⟨206177982382536081566632373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137451988255024054377754915 206177982382536081566632373)
    ·
      refine ⟨19329185848362757646871785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206177982382536081566632373 19329185848362757646871785)
      ·
        refine ⟨14496889386272068235153839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19329185848362757646871785 14496889386272068235153839)
        ·
          refine ⟨21745334079408102352730759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496889386272068235153839 21745334079408102352730759)
          ·
            refine ⟨32618001119112153529096139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21745334079408102352730759 32618001119112153529096139)
            ·
              refine ⟨48927001678668230293644209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32618001119112153529096139 48927001678668230293644209)
              ·
                refine ⟨36695251259001172720233157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48927001678668230293644209 36695251259001172720233157)
                ·
                  refine ⟨6880359611062719885043717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36695251259001172720233157 6880359611062719885043717)
                  ·
                    refine ⟨1290067427074259978445697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880359611062719885043717 1290067427074259978445697)
                    ·
                      rfl

theorem cell23_7537192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_7537192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537192 prefixEnd_7537192 := by exact prefixLift 7537192
  have htrace : WordTrace (prefixWord ++ tailWord_7537192) baseStart_7537192 baseEnd_7537192 := by
    simpa [prefixWord, tailWord_7537192, baseEnd_7537192] using wordTrace_append hprefix tailTrace_7537192
  have hstable : (prefixWord ++ tailWord_7537192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537192).length < 2 ^ (prefixWord ++ tailWord_7537192).sum := by decide
  have hdescent : baseEnd_7537192 < baseStart_7537192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537202 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_7537202 : Nat := 118140960795 + 7537202 * 2 ^ 59
def prefixEnd_7537202 : Nat := 4983230072969 + 3 ^ 40 * 7537202 * 2
def baseEnd_7537202 : Nat := 3870207416029324896212045

theorem tailTrace_7537202 : CollatzResearch.WordTrace tailWord_7537202 prefixEnd_7537202 3870207416029324896212045 := by
  unfold tailWord_7537202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68726085310002970115843465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183269560826674586975582573 68726085310002970115843465)
  ·
    refine ⟨51544563982502227586882599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68726085310002970115843465 51544563982502227586882599)
    ·
      refine ⟨77316845973753341380323899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51544563982502227586882599 77316845973753341380323899)
      ·
        refine ⟨115975268960630012070485849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77316845973753341380323899 115975268960630012070485849)
        ·
          refine ⟨86981451720472509052864387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115975268960630012070485849 86981451720472509052864387)
          ·
            refine ⟨130472177580708763579296581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86981451720472509052864387 130472177580708763579296581)
            ·
              refine ⟨24463533296382893171118109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130472177580708763579296581 24463533296382893171118109)
              ·
                refine ⟨9173824986143584939169291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24463533296382893171118109 9173824986143584939169291)
                ·
                  refine ⟨13760737479215377408753937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9173824986143584939169291 13760737479215377408753937)
                  ·
                    refine ⟨10320553109411533056565453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13760737479215377408753937 10320553109411533056565453)
                    ·
                      refine ⟨3870207416029324896212045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320553109411533056565453 3870207416029324896212045)
                      ·
                        rfl

theorem cell23_7537202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_7537202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537202 prefixEnd_7537202 := by exact prefixLift 7537202
  have htrace : WordTrace (prefixWord ++ tailWord_7537202) baseStart_7537202 baseEnd_7537202 := by
    simpa [prefixWord, tailWord_7537202, baseEnd_7537202] using wordTrace_append hprefix tailTrace_7537202
  have hstable : (prefixWord ++ tailWord_7537202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537202).length < 2 ^ (prefixWord ++ tailWord_7537202).sum := by decide
  have hdescent : baseEnd_7537202 < baseStart_7537202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537222 : List Nat := [6, 1, 1, 1, 2, 1, 1, 10]
def baseStart_7537222 : Nat := 118140960795 + 7537222 * 2 ^ 59
def prefixEnd_7537222 : Nat := 4983230072969 + 3 ^ 40 * 7537222 * 2
def baseEnd_7537222 : Nat := 143341395764533882146739

theorem tailTrace_7537222 : CollatzResearch.WordTrace tailWord_7537222 prefixEnd_7537222 143341395764533882146739 := by
  unfold tailWord_7537222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590783459373106996221935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183270047133292949252734613 8590783459373106996221935)
  ·
    refine ⟨12886175189059660494332903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8590783459373106996221935 12886175189059660494332903)
    ·
      refine ⟨19329262783589490741499355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12886175189059660494332903 19329262783589490741499355)
      ·
        refine ⟨28993894175384236112249033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19329262783589490741499355 28993894175384236112249033)
        ·
          refine ⟨21745420631538177084186775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28993894175384236112249033 21745420631538177084186775)
          ·
            refine ⟨32618130947307265626280163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21745420631538177084186775 32618130947307265626280163)
            ·
              refine ⟨48927196420960898439420245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32618130947307265626280163 48927196420960898439420245)
              ·
                refine ⟨143341395764533882146739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48927196420960898439420245 143341395764533882146739)
                ·
                  rfl

theorem cell23_7537222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_7537222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537222 prefixEnd_7537222 := by exact prefixLift 7537222
  have htrace : WordTrace (prefixWord ++ tailWord_7537222) baseStart_7537222 baseEnd_7537222 := by
    simpa [prefixWord, tailWord_7537222, baseEnd_7537222] using wordTrace_append hprefix tailTrace_7537222
  have hstable : (prefixWord ++ tailWord_7537222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537222).length < 2 ^ (prefixWord ++ tailWord_7537222).sum := by decide
  have hdescent : baseEnd_7537222 < baseStart_7537222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537225 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 9, 2]
def baseStart_7537225 : Nat := 118140960795 + 7537225 * 2 ^ 59
def prefixEnd_7537225 : Nat := 4983230072969 + 3 ^ 40 * 7537225 * 2
def baseEnd_7537225 : Nat := 3870219226084378306224439

theorem tailTrace_7537225 : CollatzResearch.WordTrace tailWord_7537225 prefixEnd_7537225 3870219226084378306224439 := by
  unfold tailWord_7537225
  simp only [CollatzResearch.WordTrace]
  refine ⟨274905180118928555391461129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183270120079285703594307419 274905180118928555391461129)
  ·
    refine ⟨206178885089196416543595847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274905180118928555391461129 206178885089196416543595847)
    ·
      refine ⟨309268327633794624815393771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206178885089196416543595847 309268327633794624815393771)
      ·
        refine ⟨463902491450691937223090657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309268327633794624815393771 463902491450691937223090657)
        ·
          refine ⟨347926868588018952917317993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463902491450691937223090657 347926868588018952917317993)
          ·
            refine ⟨260945151441014214687988495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347926868588018952917317993 260945151441014214687988495)
            ·
              refine ⟨391417727161521322031982743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260945151441014214687988495 391417727161521322031982743)
              ·
                refine ⟨587126590742281983047974115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391417727161521322031982743 587126590742281983047974115)
                ·
                  refine ⟨880689886113422974571961173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587126590742281983047974115 880689886113422974571961173)
                  ·
                    refine ⟨5160292301445837741632585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 880689886113422974571961173 5160292301445837741632585)
                    ·
                      refine ⟨3870219226084378306224439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160292301445837741632585 3870219226084378306224439)
                      ·
                        rfl

theorem cell23_7537225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 9, 2].length) (baseStart_7537225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537225 prefixEnd_7537225 := by exact prefixLift 7537225
  have htrace : WordTrace (prefixWord ++ tailWord_7537225) baseStart_7537225 baseEnd_7537225 := by
    simpa [prefixWord, tailWord_7537225, baseEnd_7537225] using wordTrace_append hprefix tailTrace_7537225
  have hstable : (prefixWord ++ tailWord_7537225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537225).length < 2 ^ (prefixWord ++ tailWord_7537225).sum := by decide
  have hdescent : baseEnd_7537225 < baseStart_7537225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537266 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_7537266 : Nat := 118140960795 + 7537266 * 2 ^ 59
def prefixEnd_7537266 : Nat := 4983230072969 + 3 ^ 40 * 7537266 * 2
def baseEnd_7537266 : Nat := 3870240278791212645811751

theorem tailTrace_7537266 : CollatzResearch.WordTrace tailWord_7537266 prefixEnd_7537266 3870240278791212645811751 := by
  unfold tailWord_7537266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68726668877945004848425913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183271117007853346262469101 68726668877945004848425913)
  ·
    refine ⟨51545001658458753636319435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68726668877945004848425913 51545001658458753636319435)
    ·
      refine ⟨77317502487688130454479153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51545001658458753636319435 77317502487688130454479153)
      ·
        refine ⟨57988126865766097840859365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77317502487688130454479153 57988126865766097840859365)
        ·
          refine ⟨10872773787331143345161131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57988126865766097840859365 10872773787331143345161131)
          ·
            refine ⟨16309160680996715017741697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872773787331143345161131 16309160680996715017741697)
            ·
              refine ⟨12231870510747536263306273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16309160680996715017741697 12231870510747536263306273)
              ·
                refine ⟨9173902883060652197479705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12231870510747536263306273 9173902883060652197479705)
                ·
                  refine ⟨6880427162295489148109779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9173902883060652197479705 6880427162295489148109779)
                  ·
                    refine ⟨10320640743443233722164669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880427162295489148109779 10320640743443233722164669)
                    ·
                      refine ⟨3870240278791212645811751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320640743443233722164669 3870240278791212645811751)
                      ·
                        rfl

theorem cell23_7537266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_7537266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537266 prefixEnd_7537266 := by exact prefixLift 7537266
  have htrace : WordTrace (prefixWord ++ tailWord_7537266) baseStart_7537266 baseEnd_7537266 := by
    simpa [prefixWord, tailWord_7537266, baseEnd_7537266] using wordTrace_append hprefix tailTrace_7537266
  have hstable : (prefixWord ++ tailWord_7537266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537266).length < 2 ^ (prefixWord ++ tailWord_7537266).sum := by decide
  have hdescent : baseEnd_7537266 < baseStart_7537266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537285 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_7537285 : Nat := 118140960795 + 7537285 * 2 ^ 59
def prefixEnd_7537285 : Nat := 4983230072969 + 3 ^ 40 * 7537285 * 2
def baseEnd_7537285 : Nat := 3870250034923648071474163

theorem tailTrace_7537285 : CollatzResearch.WordTrace tailWord_7537285 prefixEnd_7537285 3870250034923648071474163 := by
  unfold tailWord_7537285
  simp only [CollatzResearch.WordTrace]
  refine ⟨274907368498711185638645309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183271578999140790425763539 274907368498711185638645309)
  ·
    refine ⟨103090263187016694614491991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274907368498711185638645309 103090263187016694614491991)
    ·
      refine ⟨154635394780525041921737987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103090263187016694614491991 154635394780525041921737987)
      ·
        refine ⟨231953092170787562882606981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154635394780525041921737987 231953092170787562882606981)
        ·
          refine ⟨43491204782022668040488809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231953092170787562882606981 43491204782022668040488809)
          ·
            refine ⟨32618403586517001030366607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43491204782022668040488809 32618403586517001030366607)
            ·
              refine ⟨48927605379775501545549911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32618403586517001030366607 48927605379775501545549911)
              ·
                refine ⟨73391408069663252318324867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48927605379775501545549911 73391408069663252318324867)
                ·
                  refine ⟨110087112104494878477487301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73391408069663252318324867 110087112104494878477487301)
                  ·
                    refine ⟨20641333519592789714528869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110087112104494878477487301 20641333519592789714528869)
                    ·
                      refine ⟨3870250034923648071474163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20641333519592789714528869 3870250034923648071474163)
                      ·
                        rfl

theorem cell23_7537285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_7537285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537285 prefixEnd_7537285 := by exact prefixLift 7537285
  have htrace : WordTrace (prefixWord ++ tailWord_7537285) baseStart_7537285 baseEnd_7537285 := by
    simpa [prefixWord, tailWord_7537285, baseEnd_7537285] using wordTrace_append hprefix tailTrace_7537285
  have hstable : (prefixWord ++ tailWord_7537285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537285).length < 2 ^ (prefixWord ++ tailWord_7537285).sum := by decide
  have hdescent : baseEnd_7537285 < baseStart_7537285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537305 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_7537305 : Nat := 118140960795 + 7537305 * 2 ^ 59
def prefixEnd_7537305 : Nat := 4983230072969 + 3 ^ 40 * 7537305 * 2
def baseEnd_7537305 : Nat := 3870260304536737993224071

theorem tailTrace_7537305 : CollatzResearch.WordTrace tailWord_7537305 prefixEnd_7537305 3870260304536737993224071 := by
  unfold tailWord_7537305
  simp only [CollatzResearch.WordTrace]
  refine ⟨274908097958638729054373369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183272065305759152702915579 274908097958638729054373369)
  ·
    refine ⟨206181073468979046790780027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274908097958638729054373369 206181073468979046790780027)
    ·
      refine ⟨309271610203468570186170041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206181073468979046790780027 309271610203468570186170041)
      ·
        refine ⟨231953707652601427639627531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309271610203468570186170041 231953707652601427639627531)
        ·
          refine ⟨347930561478902141459441297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231953707652601427639627531 347930561478902141459441297)
          ·
            refine ⟨260947921109176606094580973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347930561478902141459441297 260947921109176606094580973)
            ·
              refine ⟨97855470415941227285467865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260947921109176606094580973 97855470415941227285467865)
              ·
                refine ⟨73391602811955920464100899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97855470415941227285467865 73391602811955920464100899)
                ·
                  refine ⟨110087404217933880696151349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73391602811955920464100899 110087404217933880696151349)
                  ·
                    refine ⟨10320694145431301315264189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110087404217933880696151349 10320694145431301315264189)
                    ·
                      refine ⟨3870260304536737993224071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10320694145431301315264189 3870260304536737993224071)
                      ·
                        rfl

theorem cell23_7537305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_7537305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537305 prefixEnd_7537305 := by exact prefixLift 7537305
  have htrace : WordTrace (prefixWord ++ tailWord_7537305) baseStart_7537305 baseEnd_7537305 := by
    simpa [prefixWord, tailWord_7537305, baseEnd_7537305] using wordTrace_append hprefix tailTrace_7537305
  have hstable : (prefixWord ++ tailWord_7537305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537305).length < 2 ^ (prefixWord ++ tailWord_7537305).sum := by decide
  have hdescent : baseEnd_7537305 < baseStart_7537305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537329 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 7]
def baseStart_7537329 : Nat := 118140960795 + 7537329 * 2 ^ 59
def prefixEnd_7537329 : Nat := 4983230072969 + 3 ^ 40 * 7537329 * 2
def baseEnd_7537329 : Nat := 430030292008049544369329

theorem tailTrace_7537329 : CollatzResearch.WordTrace tailWord_7537329 prefixEnd_7537329 430030292008049544369329 := by
  unfold tailWord_7537329
  simp only [CollatzResearch.WordTrace]
  refine ⟨274908973310551781153247041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183272648873701187435498027 274908973310551781153247041)
  ·
    refine ⟨206181729982913835864935281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274908973310551781153247041 206181729982913835864935281)
    ·
      refine ⟨154636297487185376898701461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206181729982913835864935281 154636297487185376898701461)
      ·
        refine ⟨7248576444711814542126631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154636297487185376898701461 7248576444711814542126631)
        ·
          refine ⟨10872864667067721813189947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248576444711814542126631 10872864667067721813189947)
          ·
            refine ⟨16309297000601582719784921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872864667067721813189947 16309297000601582719784921)
            ·
              refine ⟨12231972750451187039838691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16309297000601582719784921 12231972750451187039838691)
              ·
                refine ⟨18347959125676780559758037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12231972750451187039838691 18347959125676780559758037)
                ·
                  refine ⟨430030292008049544369329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18347959125676780559758037 430030292008049544369329)
                  ·
                    rfl

theorem cell23_7537329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_7537329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537329 prefixEnd_7537329 := by exact prefixLift 7537329
  have htrace : WordTrace (prefixWord ++ tailWord_7537329) baseStart_7537329 baseEnd_7537329 := by
    simpa [prefixWord, tailWord_7537329, baseEnd_7537329] using wordTrace_append hprefix tailTrace_7537329
  have hstable : (prefixWord ++ tailWord_7537329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537329).length < 2 ^ (prefixWord ++ tailWord_7537329).sum := by decide
  have hdescent : baseEnd_7537329 < baseStart_7537329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537379 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7537379 : Nat := 118140960795 + 7537379 * 2 ^ 59
def prefixEnd_7537379 : Nat := 4983230072969 + 3 ^ 40 * 7537379 * 2
def baseEnd_7537379 : Nat := 3870298302105170703698731

theorem tailTrace_7537379 : CollatzResearch.WordTrace tailWord_7537379 prefixEnd_7537379 3870298302105170703698731 := by
  unfold tailWord_7537379
  simp only [CollatzResearch.WordTrace]
  refine ⟨274910796960370639692567191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183273864640247093128378127 274910796960370639692567191)
  ·
    refine ⟨412366195440555959538850787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274910796960370639692567191 412366195440555959538850787)
    ·
      refine ⟨618549293160833939308276181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412366195440555959538850787 618549293160833939308276181)
      ·
        refine ⟨14497249058457045452537723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 618549293160833939308276181 14497249058457045452537723)
        ·
          refine ⟨21745873587685568178806585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497249058457045452537723 21745873587685568178806585)
          ·
            refine ⟨16309405190764176134104939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21745873587685568178806585 16309405190764176134104939)
            ·
              refine ⟨24464107786146264201157409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309405190764176134104939 24464107786146264201157409)
              ·
                refine ⟨18348080839609698150868057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24464107786146264201157409 18348080839609698150868057)
                ·
                  refine ⟨13761060629707273613151043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18348080839609698150868057 13761060629707273613151043)
                  ·
                    refine ⟨20641590944560910419726565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13761060629707273613151043 20641590944560910419726565)
                    ·
                      refine ⟨3870298302105170703698731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20641590944560910419726565 3870298302105170703698731)
                      ·
                        rfl

theorem cell23_7537379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7537379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537379 prefixEnd_7537379 := by exact prefixLift 7537379
  have htrace : WordTrace (prefixWord ++ tailWord_7537379) baseStart_7537379 baseEnd_7537379 := by
    simpa [prefixWord, tailWord_7537379, baseEnd_7537379] using wordTrace_append hprefix tailTrace_7537379
  have hstable : (prefixWord ++ tailWord_7537379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537379).length < 2 ^ (prefixWord ++ tailWord_7537379).sum := by decide
  have hdescent : baseEnd_7537379 < baseStart_7537379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537385 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 8]
def baseStart_7537385 : Nat := 118140960795 + 7537385 * 2 ^ 59
def prefixEnd_7537385 : Nat := 4983230072969 + 3 ^ 40 * 7537385 * 2
def baseEnd_7537385 : Nat := 430033486998788631135967

theorem tailTrace_7537385 : CollatzResearch.WordTrace tailWord_7537385 prefixEnd_7537385 430033486998788631135967 := by
  unfold tailWord_7537385
  simp only [CollatzResearch.WordTrace]
  refine ⟨274911015798348902717285609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183274010532232601811523739 274911015798348902717285609)
  ·
    refine ⟨206183261848761677037964207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274911015798348902717285609 206183261848761677037964207)
    ·
      refine ⟨309274892773142515556946311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206183261848761677037964207 309274892773142515556946311)
      ·
        refine ⟨463912339159713773335419467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309274892773142515556946311 463912339159713773335419467)
        ·
          refine ⟨695868508739570660003129201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463912339159713773335419467 695868508739570660003129201)
          ·
            refine ⟨521901381554677995002346901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695868508739570660003129201 521901381554677995002346901)
            ·
              refine ⟨24464127260375531015735011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 521901381554677995002346901 24464127260375531015735011)
              ·
                refine ⟨36696190890563296523602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24464127260375531015735011 36696190890563296523602517)
                ·
                  refine ⟨430033486998788631135967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36696190890563296523602517 430033486998788631135967)
                  ·
                    rfl

theorem cell23_7537385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_7537385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537385 prefixEnd_7537385 := by exact prefixLift 7537385
  have htrace : WordTrace (prefixWord ++ tailWord_7537385) baseStart_7537385 baseEnd_7537385 := by
    simpa [prefixWord, tailWord_7537385, baseEnd_7537385] using wordTrace_append hprefix tailTrace_7537385
  have hstable : (prefixWord ++ tailWord_7537385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537385).length < 2 ^ (prefixWord ++ tailWord_7537385).sum := by decide
  have hdescent : baseEnd_7537385 < baseStart_7537385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537452 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 4]
def baseStart_7537452 : Nat := 118140960795 + 7537452 * 2 ^ 59
def prefixEnd_7537452 : Nat := 4983230072969 + 3 ^ 40 * 7537452 * 2
def baseEnd_7537452 : Nat := 3870335786192948918085895

theorem tailTrace_7537452 : CollatzResearch.WordTrace tailWord_7537452 prefixEnd_7537452 3870335786192948918085895 := by
  unfold tailWord_7537452
  simp only [CollatzResearch.WordTrace]
  refine ⟨137456729744553086579987305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183275639659404115439983073 137456729744553086579987305)
  ·
    refine ⟨103092547308414814934990479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137456729744553086579987305 103092547308414814934990479)
    ·
      refine ⟨154638820962622222402485719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103092547308414814934990479 154638820962622222402485719)
      ·
        refine ⟨231958231443933333603728579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154638820962622222402485719 231958231443933333603728579)
        ·
          refine ⟨347937347165900000405592869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231958231443933333603728579 347937347165900000405592869)
          ·
            refine ⟨65238252593606250076048663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347937347165900000405592869 65238252593606250076048663)
            ·
              refine ⟨97857378890409375114072995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65238252593606250076048663 97857378890409375114072995)
              ·
                refine ⟨146786068335614062671109493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97857378890409375114072995 146786068335614062671109493)
                ·
                  refine ⟨13761193906463818375416515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146786068335614062671109493 13761193906463818375416515)
                  ·
                    refine ⟨20641790859695727563124773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13761193906463818375416515 20641790859695727563124773)
                    ·
                      refine ⟨3870335786192948918085895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20641790859695727563124773 3870335786192948918085895)
                      ·
                        rfl

theorem cell23_7537452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_7537452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537452 prefixEnd_7537452 := by exact prefixLift 7537452
  have htrace : WordTrace (prefixWord ++ tailWord_7537452) baseStart_7537452 baseEnd_7537452 := by
    simpa [prefixWord, tailWord_7537452, baseEnd_7537452] using wordTrace_append hprefix tailTrace_7537452
  have hstable : (prefixWord ++ tailWord_7537452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537452).length < 2 ^ (prefixWord ++ tailWord_7537452).sum := by decide
  have hdescent : baseEnd_7537452 < baseStart_7537452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537473 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7537473 : Nat := 118140960795 + 7537473 * 2 ^ 59
def prefixEnd_7537473 : Nat := 4983230072969 + 3 ^ 40 * 7537473 * 2
def baseEnd_7537473 : Nat := 3870346569286693335923299

theorem tailTrace_7537473 : CollatzResearch.WordTrace tailWord_7537473 prefixEnd_7537473 3870346569286693335923299 := by
  unfold tailWord_7537473
  simp only [CollatzResearch.WordTrace]
  refine ⟨274914225422030093746489073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183276150281353395830992715 274914225422030093746489073)
  ·
    refine ⟨206185669066522570309866805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274914225422030093746489073 206185669066522570309866805)
    ·
      refine ⟨19329906474986490966550013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206185669066522570309866805 19329906474986490966550013)
      ·
        refine ⟨7248714928119934112456255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19329906474986490966550013 7248714928119934112456255)
        ·
          refine ⟨10873072392179901168684383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248714928119934112456255 10873072392179901168684383)
          ·
            refine ⟨16309608588269851753026575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873072392179901168684383 16309608588269851753026575)
            ·
              refine ⟨24464412882404777629539863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309608588269851753026575 24464412882404777629539863)
              ·
                refine ⟨36696619323607166444309795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24464412882404777629539863 36696619323607166444309795)
                ·
                  refine ⟨55044928985410749666464693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36696619323607166444309795 55044928985410749666464693)
                  ·
                    refine ⟨5160462092382257781231065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55044928985410749666464693 5160462092382257781231065)
                    ·
                      refine ⟨3870346569286693335923299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160462092382257781231065 3870346569286693335923299)
                      ·
                        rfl

theorem cell23_7537473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7537473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537473 prefixEnd_7537473 := by exact prefixLift 7537473
  have htrace : WordTrace (prefixWord ++ tailWord_7537473) baseStart_7537473 baseEnd_7537473 := by
    simpa [prefixWord, tailWord_7537473, baseEnd_7537473] using wordTrace_append hprefix tailTrace_7537473
  have hstable : (prefixWord ++ tailWord_7537473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537473).length < 2 ^ (prefixWord ++ tailWord_7537473).sum := by decide
  have hdescent : baseEnd_7537473 < baseStart_7537473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537482 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_7537482 : Nat := 118140960795 + 7537482 * 2 ^ 59
def prefixEnd_7537482 : Nat := 4983230072969 + 3 ^ 40 * 7537482 * 2
def baseEnd_7537482 : Nat := 3870351190612583800710757

theorem tailTrace_7537482 : CollatzResearch.WordTrace tailWord_7537482 prefixEnd_7537482 3870351190612583800710757 := by
  unfold tailWord_7537482
  simp only [CollatzResearch.WordTrace]
  refine ⟨68728638419749372070891675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183276369119331658855711133 68728638419749372070891675)
  ·
    refine ⟨103092957629624058106337513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68728638419749372070891675 103092957629624058106337513)
    ·
      refine ⟨77319718222218043579753135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103092957629624058106337513 77319718222218043579753135)
      ·
        refine ⟨115979577333327065369629703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77319718222218043579753135 115979577333327065369629703)
        ·
          refine ⟨173969365999990598054444555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115979577333327065369629703 173969365999990598054444555)
          ·
            refine ⟨260954048999985897081666833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173969365999990598054444555 260954048999985897081666833)
            ·
              refine ⟨195715536749989422811250125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260954048999985897081666833 195715536749989422811250125)
              ·
                refine ⟨73393326281246033554218797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195715536749989422811250125 73393326281246033554218797)
                ·
                  refine ⟨27522497355467262582832049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73393326281246033554218797 27522497355467262582832049)
                  ·
                    refine ⟨20641873016600446937124037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27522497355467262582832049 20641873016600446937124037)
                    ·
                      refine ⟨3870351190612583800710757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20641873016600446937124037 3870351190612583800710757)
                      ·
                        rfl

theorem cell23_7537482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_7537482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537482 prefixEnd_7537482 := by exact prefixLift 7537482
  have htrace : WordTrace (prefixWord ++ tailWord_7537482) baseStart_7537482 baseEnd_7537482 := by
    simpa [prefixWord, tailWord_7537482, baseEnd_7537482] using wordTrace_append hprefix tailTrace_7537482
  have hstable : (prefixWord ++ tailWord_7537482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537482).length < 2 ^ (prefixWord ++ tailWord_7537482).sum := by decide
  have hdescent : baseEnd_7537482 < baseStart_7537482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537503 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 1, 2, 2]
def baseStart_7537503 : Nat := 118140960795 + 7537503 * 2 ^ 59
def prefixEnd_7537503 : Nat := 4983230072969 + 3 ^ 40 * 7537503 * 2
def baseEnd_7537503 : Nat := 3870361973706328218548161

theorem tailTrace_7537503 : CollatzResearch.WordTrace tailWord_7537503 prefixEnd_7537503 3870361973706328218548161 := by
  unfold tailWord_7537503
  simp only [CollatzResearch.WordTrace]
  refine ⟨274915319611921408870081163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183276879741280939246720775 274915319611921408870081163)
  ·
    refine ⟨412372979417882113305121745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274915319611921408870081163 412372979417882113305121745)
    ·
      refine ⟨309279734563411584978841309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412372979417882113305121745 309279734563411584978841309)
      ·
        refine ⟨115979900461279344367065491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309279734563411584978841309 115979900461279344367065491)
        ·
          refine ⟨173969850691919016550598237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115979900461279344367065491 173969850691919016550598237)
          ·
            refine ⟨65238694009469631206474339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173969850691919016550598237 65238694009469631206474339)
            ·
              refine ⟨97858041014204446809711509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65238694009469631206474339 97858041014204446809711509)
              ·
                refine ⟨4587095672540833444205227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97858041014204446809711509 4587095672540833444205227)
                ·
                  refine ⟨6880643508811250166307841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587095672540833444205227 6880643508811250166307841)
                  ·
                    refine ⟨5160482631608437624730881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6880643508811250166307841 5160482631608437624730881)
                    ·
                      refine ⟨3870361973706328218548161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160482631608437624730881 3870361973706328218548161)
                      ·
                        rfl

theorem cell23_7537503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_7537503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537503 prefixEnd_7537503 := by exact prefixLift 7537503
  have htrace : WordTrace (prefixWord ++ tailWord_7537503) baseStart_7537503 baseEnd_7537503 := by
    simpa [prefixWord, tailWord_7537503, baseEnd_7537503] using wordTrace_append hprefix tailTrace_7537503
  have hstable : (prefixWord ++ tailWord_7537503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537503).length < 2 ^ (prefixWord ++ tailWord_7537503).sum := by decide
  have hdescent : baseEnd_7537503 < baseStart_7537503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537506 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7537506 : Nat := 118140960795 + 7537506 * 2 ^ 59
def prefixEnd_7537506 : Nat := 4983230072969 + 3 ^ 40 * 7537506 * 2
def baseEnd_7537506 : Nat := 3870363514148291706810647

theorem tailTrace_7537506 : CollatzResearch.WordTrace tailWord_7537506 prefixEnd_7537506 3870363514148291706810647 := by
  unfold tailWord_7537506
  simp only [CollatzResearch.WordTrace]
  refine ⟨68728857257727635095610093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183276952687273693588293581 68728857257727635095610093)
  ·
    refine ⟨25773321471647863160853785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68728857257727635095610093 25773321471647863160853785)
    ·
      refine ⟨19329991103735897370640339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25773321471647863160853785 19329991103735897370640339)
      ·
        refine ⟨28994986655603846055960509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19329991103735897370640339 28994986655603846055960509)
        ·
          refine ⟨10873119995851442270985191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28994986655603846055960509 10873119995851442270985191)
          ·
            refine ⟨16309679993777163406477787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873119995851442270985191 16309679993777163406477787)
            ·
              refine ⟨24464519990665745109716681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309679993777163406477787 24464519990665745109716681)
              ·
                refine ⟨18348389992999308832287511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24464519990665745109716681 18348389992999308832287511)
                ·
                  refine ⟨27522584989498963248431267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18348389992999308832287511 27522584989498963248431267)
                  ·
                    refine ⟨41283877484248444872646901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27522584989498963248431267 41283877484248444872646901)
                    ·
                      refine ⟨3870363514148291706810647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41283877484248444872646901 3870363514148291706810647)
                      ·
                        rfl

theorem cell23_7537506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7537506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537506 prefixEnd_7537506 := by exact prefixLift 7537506
  have htrace : WordTrace (prefixWord ++ tailWord_7537506) baseStart_7537506 baseEnd_7537506 := by
    simpa [prefixWord, tailWord_7537506, baseEnd_7537506] using wordTrace_append hprefix tailTrace_7537506
  have hstable : (prefixWord ++ tailWord_7537506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537506).length < 2 ^ (prefixWord ++ tailWord_7537506).sum := by decide
  have hdescent : baseEnd_7537506 < baseStart_7537506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537522 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_7537522 : Nat := 118140960795 + 7537522 * 2 ^ 59
def prefixEnd_7537522 : Nat := 4983230072969 + 3 ^ 40 * 7537522 * 2
def baseEnd_7537522 : Nat := 1290123909946254548070191

theorem tailTrace_7537522 : CollatzResearch.WordTrace tailWord_7537522 prefixEnd_7537522 1290123909946254548070191 := by
  unfold tailWord_7537522
  simp only [CollatzResearch.WordTrace]
  refine ⟨68729003149713143778755705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183277341732568383410015213 68729003149713143778755705)
  ·
    refine ⟨51546752362284857834066779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68729003149713143778755705 51546752362284857834066779)
    ·
      refine ⟨77320128543427286751100169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51546752362284857834066779 77320128543427286751100169)
      ·
        refine ⟨57990096407570465063325127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77320128543427286751100169 57990096407570465063325127)
        ·
          refine ⟨86985144611355697594987691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57990096407570465063325127 86985144611355697594987691)
          ·
            refine ⟨130477716917033546392481537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86985144611355697594987691 130477716917033546392481537)
            ·
              refine ⟨97858287687775159794361153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130477716917033546392481537 97858287687775159794361153)
              ·
                refine ⟨73393715765831369845770865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97858287687775159794361153 73393715765831369845770865)
                ·
                  refine ⟨55045286824373527384328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73393715765831369845770865 55045286824373527384328149)
                  ·
                    refine ⟨1290123909946254548070191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55045286824373527384328149 1290123909946254548070191)
                    ·
                      rfl

theorem cell23_7537522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_7537522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537522 prefixEnd_7537522 := by exact prefixLift 7537522
  have htrace : WordTrace (prefixWord ++ tailWord_7537522) baseStart_7537522 baseEnd_7537522 := by
    simpa [prefixWord, tailWord_7537522, baseEnd_7537522] using wordTrace_append hprefix tailTrace_7537522
  have hstable : (prefixWord ++ tailWord_7537522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537522).length < 2 ^ (prefixWord ++ tailWord_7537522).sum := by decide
  have hdescent : baseEnd_7537522 < baseStart_7537522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537526 : List Nat := [5, 1, 1, 3, 1, 1, 4, 7]
def baseStart_7537526 : Nat := 118140960795 + 7537526 * 2 ^ 59
def prefixEnd_7537526 : Nat := 4983230072969 + 3 ^ 40 * 7537526 * 2
def baseEnd_7537526 : Nat := 143347177176347467724465

theorem tailTrace_7537526 : CollatzResearch.WordTrace tailWord_7537526 prefixEnd_7537526 143347177176347467724465 := by
  unfold tailWord_7537526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182259905677380237385527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183277438993892055865445621 17182259905677380237385527)
  ·
    refine ⟨25773389858516070356078291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182259905677380237385527 25773389858516070356078291)
    ·
      refine ⟨38660084787774105534117437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25773389858516070356078291 38660084787774105534117437)
      ·
        refine ⟨14497531795415289575294039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38660084787774105534117437 14497531795415289575294039)
        ·
          refine ⟨21746297693122934362941059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497531795415289575294039 21746297693122934362941059)
          ·
            refine ⟨32619446539684401544411589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21746297693122934362941059 32619446539684401544411589)
            ·
              refine ⟨6116146226190825289577173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32619446539684401544411589 6116146226190825289577173)
              ·
                refine ⟨143347177176347467724465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6116146226190825289577173 143347177176347467724465)
                ·
                  rfl

theorem cell23_7537526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_7537526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537526 prefixEnd_7537526 := by exact prefixLift 7537526
  have htrace : WordTrace (prefixWord ++ tailWord_7537526) baseStart_7537526 baseEnd_7537526 := by
    simpa [prefixWord, tailWord_7537526, baseEnd_7537526] using wordTrace_append hprefix tailTrace_7537526
  have hstable : (prefixWord ++ tailWord_7537526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537526).length < 2 ^ (prefixWord ++ tailWord_7537526).sum := by decide
  have hdescent : baseEnd_7537526 < baseStart_7537526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537554 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7537554 : Nat := 118140960795 + 7537554 * 2 ^ 59
def prefixEnd_7537554 : Nat := 4983230072969 + 3 ^ 40 * 7537554 * 2
def baseEnd_7537554 : Nat := 3870388161219707519010427

theorem tailTrace_7537554 : CollatzResearch.WordTrace tailWord_7537554 prefixEnd_7537554 3870388161219707519010427 := by
  unfold tailWord_7537554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68729294933684161145046929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183278119823157763053458477 68729294933684161145046929)
  ·
    refine ⟨51546971200263120858785197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68729294933684161145046929 51546971200263120858785197)
    ·
      refine ⟨19330114200098670322044449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51546971200263120858785197 19330114200098670322044449)
      ·
        refine ⟨14497585650074002741533337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19330114200098670322044449 14497585650074002741533337)
        ·
          refine ⟨10873189237555502056150003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14497585650074002741533337 10873189237555502056150003)
          ·
            refine ⟨16309783856333253084225005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873189237555502056150003 16309783856333253084225005)
            ·
              refine ⟨6116168946124969906584377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16309783856333253084225005 6116168946124969906584377)
              ·
                refine ⟨4587126709593727429938283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116168946124969906584377 4587126709593727429938283)
                ·
                  refine ⟨6880690064390591144907425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587126709593727429938283 6880690064390591144907425)
                  ·
                    refine ⟨5160517548292943358680569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6880690064390591144907425 5160517548292943358680569)
                    ·
                      refine ⟨3870388161219707519010427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160517548292943358680569 3870388161219707519010427)
                      ·
                        rfl

theorem cell23_7537554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7537554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537554 prefixEnd_7537554 := by exact prefixLift 7537554
  have htrace : WordTrace (prefixWord ++ tailWord_7537554) baseStart_7537554 baseEnd_7537554 := by
    simpa [prefixWord, tailWord_7537554, baseEnd_7537554] using wordTrace_append hprefix tailTrace_7537554
  have hstable : (prefixWord ++ tailWord_7537554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537554).length < 2 ^ (prefixWord ++ tailWord_7537554).sum := by decide
  have hdescent : baseEnd_7537554 < baseStart_7537554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537570 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_7537570 : Nat := 118140960795 + 7537570 * 2 ^ 59
def prefixEnd_7537570 : Nat := 4983230072969 + 3 ^ 40 * 7537570 * 2
def baseEnd_7537570 : Nat := 3870396376910179456410353

theorem tailTrace_7537570 : CollatzResearch.WordTrace tailWord_7537570 prefixEnd_7537570 3870396376910179456410353 := by
  unfold tailWord_7537570
  simp only [CollatzResearch.WordTrace]
  refine ⟨68729440825669669828192541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183278508868452452875180109 68729440825669669828192541)
  ·
    refine ⟨25773540309626126185572203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68729440825669669828192541 25773540309626126185572203)
    ·
      refine ⟨38660310464439189278358305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25773540309626126185572203 38660310464439189278358305)
      ·
        refine ⟨28995232848329391958768729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38660310464439189278358305 28995232848329391958768729)
        ·
          refine ⟨21746424636247043969076547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28995232848329391958768729 21746424636247043969076547)
          ·
            refine ⟨32619636954370565953614821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21746424636247043969076547 32619636954370565953614821)
            ·
              refine ⟨6116181928944481116302779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32619636954370565953614821 6116181928944481116302779)
              ·
                refine ⟨9174272893416721674454169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6116181928944481116302779 9174272893416721674454169)
                ·
                  refine ⟨6880704670062541255840627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9174272893416721674454169 6880704670062541255840627)
                  ·
                    refine ⟨10321057005093811883760941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880704670062541255840627 10321057005093811883760941)
                    ·
                      refine ⟨3870396376910179456410353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321057005093811883760941 3870396376910179456410353)
                      ·
                        rfl

theorem cell23_7537570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_7537570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537570 prefixEnd_7537570 := by exact prefixLift 7537570
  have htrace : WordTrace (prefixWord ++ tailWord_7537570) baseStart_7537570 baseEnd_7537570 := by
    simpa [prefixWord, tailWord_7537570, baseEnd_7537570] using wordTrace_append hprefix tailTrace_7537570
  have hstable : (prefixWord ++ tailWord_7537570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537570).length < 2 ^ (prefixWord ++ tailWord_7537570).sum := by decide
  have hdescent : baseEnd_7537570 < baseStart_7537570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537626 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_7537626 : Nat := 118140960795 + 7537626 * 2 ^ 59
def prefixEnd_7537626 : Nat := 4983230072969 + 3 ^ 40 * 7537626 * 2
def baseEnd_7537626 : Nat := 3870425131826831237310095

theorem tailTrace_7537626 : CollatzResearch.WordTrace tailWord_7537626 prefixEnd_7537626 3870425131826831237310095 := by
  unfold tailWord_7537626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68729951447618950219202183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183279870526983867251205821 68729951447618950219202183)
  ·
    refine ⟨103094927171428425328803275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68729951447618950219202183 103094927171428425328803275)
    ·
      refine ⟨154642390757142637993204913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103094927171428425328803275 154642390757142637993204913)
      ·
        refine ⟨115981793067856978494903685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154642390757142637993204913 115981793067856978494903685)
        ·
          refine ⟨21746586200223183467794441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115981793067856978494903685 21746586200223183467794441)
          ·
            refine ⟨16309939650167387600845831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21746586200223183467794441 16309939650167387600845831)
            ·
              refine ⟨24464909475251081401268747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309939650167387600845831 24464909475251081401268747)
              ·
                refine ⟨36697364212876622101903121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24464909475251081401268747 36697364212876622101903121)
                ·
                  refine ⟨27523023159657466576427341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36697364212876622101903121 27523023159657466576427341)
                  ·
                    refine ⟨10321133684871549966160253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27523023159657466576427341 10321133684871549966160253)
                    ·
                      refine ⟨3870425131826831237310095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321133684871549966160253 3870425131826831237310095)
                      ·
                        rfl

theorem cell23_7537626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_7537626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537626 prefixEnd_7537626 := by exact prefixLift 7537626
  have htrace : WordTrace (prefixWord ++ tailWord_7537626) baseStart_7537626 baseEnd_7537626 := by
    simpa [prefixWord, tailWord_7537626, baseEnd_7537626] using wordTrace_append hprefix tailTrace_7537626
  have hstable : (prefixWord ++ tailWord_7537626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537626).length < 2 ^ (prefixWord ++ tailWord_7537626).sum := by decide
  have hdescent : baseEnd_7537626 < baseStart_7537626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537646 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_7537646 : Nat := 118140960795 + 7537646 * 2 ^ 59
def prefixEnd_7537646 : Nat := 4983230072969 + 3 ^ 40 * 7537646 * 2
def baseEnd_7537646 : Nat := 1290145133813307053020001

theorem tailTrace_7537646 : CollatzResearch.WordTrace tailWord_7537646 prefixEnd_7537646 1290145133813307053020001 := by
  unfold tailWord_7537646
  simp only [CollatzResearch.WordTrace]
  refine ⟨34365066906300418036567099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183280356833602229528357861 34365066906300418036567099)
  ·
    refine ⟨51547600359450627054850649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34365066906300418036567099 51547600359450627054850649)
    ·
      refine ⟨38660700269587970291137987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51547600359450627054850649 38660700269587970291137987)
      ·
        refine ⟨57991050404381955436706981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38660700269587970291137987 57991050404381955436706981)
        ·
          refine ⟨10873321950821616644382559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57991050404381955436706981 10873321950821616644382559)
          ·
            refine ⟨16309982926232424966573839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873321950821616644382559 16309982926232424966573839)
            ·
              refine ⟨24464974389348637449860759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309982926232424966573839 24464974389348637449860759)
              ·
                refine ⟨36697461584022956174791139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24464974389348637449860759 36697461584022956174791139)
                ·
                  refine ⟨55046192376034434262186709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36697461584022956174791139 55046192376034434262186709)
                  ·
                    refine ⟨1290145133813307053020001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55046192376034434262186709 1290145133813307053020001)
                    ·
                      rfl

theorem cell23_7537646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_7537646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537646 prefixEnd_7537646 := by exact prefixLift 7537646
  have htrace : WordTrace (prefixWord ++ tailWord_7537646) baseStart_7537646 baseEnd_7537646 := by
    simpa [prefixWord, tailWord_7537646, baseEnd_7537646] using wordTrace_append hprefix tailTrace_7537646
  have hstable : (prefixWord ++ tailWord_7537646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537646).length < 2 ^ (prefixWord ++ tailWord_7537646).sum := by decide
  have hdescent : baseEnd_7537646 < baseStart_7537646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537650 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_7537650 : Nat := 118140960795 + 7537650 * 2 ^ 59
def prefixEnd_7537650 : Nat := 4983230072969 + 3 ^ 40 * 7537650 * 2
def baseEnd_7537650 : Nat := 430048606151393238156665

theorem tailTrace_7537650 : CollatzResearch.WordTrace tailWord_7537650 prefixEnd_7537650 430048606151393238156665 := by
  unfold tailWord_7537650
  simp only [CollatzResearch.WordTrace]
  refine ⟨68730170285597213243920601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183280454094925901983788269 68730170285597213243920601)
  ·
    refine ⟨51547627714197909932940451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68730170285597213243920601 51547627714197909932940451)
    ·
      refine ⟨77321441571296864899410677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51547627714197909932940451 77321441571296864899410677)
      ·
        refine ⟨7248885147309081084319751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77321441571296864899410677 7248885147309081084319751)
        ·
          refine ⟨10873327720963621626479627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248885147309081084319751 10873327720963621626479627)
          ·
            refine ⟨16309991581445432439719441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873327720963621626479627 16309991581445432439719441)
            ·
              refine ⟨12232493686084074329789581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16309991581445432439719441 12232493686084074329789581)
              ·
                refine ⟨4587185132281527873671093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12232493686084074329789581 4587185132281527873671093)
                ·
                  refine ⟨430048606151393238156665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4587185132281527873671093 430048606151393238156665)
                  ·
                    rfl

theorem cell23_7537650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_7537650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537650 prefixEnd_7537650 := by exact prefixLift 7537650
  have htrace : WordTrace (prefixWord ++ tailWord_7537650) baseStart_7537650 baseEnd_7537650 := by
    simpa [prefixWord, tailWord_7537650, baseEnd_7537650] using wordTrace_append hprefix tailTrace_7537650
  have hstable : (prefixWord ++ tailWord_7537650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537650).length < 2 ^ (prefixWord ++ tailWord_7537650).sum := by decide
  have hdescent : baseEnd_7537650 < baseStart_7537650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537659 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 7, 4]
def baseStart_7537659 : Nat := 118140960795 + 7537659 * 2 ^ 59
def prefixEnd_7537659 : Nat := 4983230072969 + 3 ^ 40 * 7537659 * 2
def baseEnd_7537659 : Nat := 1290147358896143202732481

theorem tailTrace_7537659 : CollatzResearch.WordTrace tailWord_7537659 prefixEnd_7537659 1290147358896143202732481 := by
  unfold tailWord_7537659
  simp only [CollatzResearch.WordTrace]
  refine ⟨274921009399356247512760031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183280672932904165008506687 274921009399356247512760031)
  ·
    refine ⟨412381514099034371269140047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274921009399356247512760031 412381514099034371269140047)
    ·
      refine ⟨618572271148551556903710071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412381514099034371269140047 618572271148551556903710071)
      ·
        refine ⟨927858406722827335355565107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618572271148551556903710071 927858406722827335355565107)
        ·
          refine ⟨1391787610084241003033347661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927858406722827335355565107 1391787610084241003033347661)
          ·
            refine ⟨521920353781590376137505373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1391787610084241003033347661 521920353781590376137505373)
            ·
              refine ⟨195720132668096391051564515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521920353781590376137505373 195720132668096391051564515)
              ·
                refine ⟨293580199002144586577346773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195720132668096391051564515 293580199002144586577346773)
                ·
                  refine ⟨6880785914112763747906565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 293580199002144586577346773 6880785914112763747906565)
                  ·
                    refine ⟨1290147358896143202732481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880785914112763747906565 1290147358896143202732481)
                    ·
                      rfl

theorem cell23_7537659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 4].length) (baseStart_7537659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537659 prefixEnd_7537659 := by exact prefixLift 7537659
  have htrace : WordTrace (prefixWord ++ tailWord_7537659) baseStart_7537659 baseEnd_7537659 := by
    simpa [prefixWord, tailWord_7537659, baseEnd_7537659] using wordTrace_append hprefix tailTrace_7537659
  have hstable : (prefixWord ++ tailWord_7537659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537659).length < 2 ^ (prefixWord ++ tailWord_7537659).sum := by decide
  have hdescent : baseEnd_7537659 < baseStart_7537659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537676 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_7537676 : Nat := 118140960795 + 7537676 * 2 ^ 59
def prefixEnd_7537676 : Nat := 4983230072969 + 3 ^ 40 * 7537676 * 2
def baseEnd_7537676 : Nat := 1290150268619852013894955

theorem tailTrace_7537676 : CollatzResearch.WordTrace tailWord_7537676 prefixEnd_7537676 1290150268619852013894955 := by
  unfold tailWord_7537676
  simp only [CollatzResearch.WordTrace]
  refine ⟨137460814720147329708064441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183281086293529772944085921 137460814720147329708064441)
  ·
    refine ⟨103095611040110497281048331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137460814720147329708064441 103095611040110497281048331)
    ·
      refine ⟨154643416560165745921572497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103095611040110497281048331 154643416560165745921572497)
      ·
        refine ⟨115982562420124309441179373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154643416560165745921572497 115982562420124309441179373)
        ·
          refine ⟨43493460907546616040442265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115982562420124309441179373 43493460907546616040442265)
          ·
            refine ⟨32620095680659962030331699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43493460907546616040442265 32620095680659962030331699)
            ·
              refine ⟨48930143520989943045497549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32620095680659962030331699 48930143520989943045497549)
              ·
                refine ⟨18348803820371228642061581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48930143520989943045497549 18348803820371228642061581)
                ·
                  refine ⟨6880801432639210740773093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18348803820371228642061581 6880801432639210740773093)
                  ·
                    refine ⟨1290150268619852013894955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880801432639210740773093 1290150268619852013894955)
                    ·
                      rfl

theorem cell23_7537676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_7537676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537676 prefixEnd_7537676 := by exact prefixLift 7537676
  have htrace : WordTrace (prefixWord ++ tailWord_7537676) baseStart_7537676 baseEnd_7537676 := by
    simpa [prefixWord, tailWord_7537676, baseEnd_7537676] using wordTrace_append hprefix tailTrace_7537676
  have hstable : (prefixWord ++ tailWord_7537676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537676).length < 2 ^ (prefixWord ++ tailWord_7537676).sum := by decide
  have hdescent : baseEnd_7537676 < baseStart_7537676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537689 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 6]
def baseStart_7537689 : Nat := 118140960795 + 7537689 * 2 ^ 59
def prefixEnd_7537689 : Nat := 4983230072969 + 3 ^ 40 * 7537689 * 2
def baseEnd_7537689 : Nat := 430050831234229387869145

theorem tailTrace_7537689 : CollatzResearch.WordTrace tailWord_7537689 prefixEnd_7537689 430050831234229387869145 := by
  unfold tailWord_7537689
  simp only [CollatzResearch.WordTrace]
  refine ⟨274922103589247562636352121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183281402392831708424234747 274922103589247562636352121)
  ·
    refine ⟨206191577691935671977264091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274922103589247562636352121 206191577691935671977264091)
    ·
      refine ⟨309287366537903507965896137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206191577691935671977264091 309287366537903507965896137)
      ·
        refine ⟨231965524903427630974422103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309287366537903507965896137 231965524903427630974422103)
        ·
          refine ⟨347948287355141446461633155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231965524903427630974422103 347948287355141446461633155)
          ·
            refine ⟨521922431032712169692449733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347948287355141446461633155 521922431032712169692449733)
            ·
              refine ⟨97860455818633531817334325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 521922431032712169692449733 97860455818633531817334325)
              ·
                refine ⟨9174417732996893607875093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97860455818633531817334325 9174417732996893607875093)
                ·
                  refine ⟨430050831234229387869145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9174417732996893607875093 430050831234229387869145)
                  ·
                    rfl

theorem cell23_7537689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_7537689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537689 prefixEnd_7537689 := by exact prefixLift 7537689
  have htrace : WordTrace (prefixWord ++ tailWord_7537689) baseStart_7537689 baseEnd_7537689 := by
    simpa [prefixWord, tailWord_7537689, baseEnd_7537689] using wordTrace_append hprefix tailTrace_7537689
  have hstable : (prefixWord ++ tailWord_7537689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537689).length < 2 ^ (prefixWord ++ tailWord_7537689).sum := by decide
  have hdescent : baseEnd_7537689 < baseStart_7537689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537703 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7537703 : Nat := 118140960795 + 7537703 * 2 ^ 59
def prefixEnd_7537703 : Nat := 4983230072969 + 3 ^ 40 * 7537703 * 2
def baseEnd_7537703 : Nat := 3870464669837227436047241

theorem tailTrace_7537703 : CollatzResearch.WordTrace tailWord_7537703 prefixEnd_7537703 3870464669837227436047241 := by
  unfold tailWord_7537703
  simp only [CollatzResearch.WordTrace]
  refine ⟨274922614211196843027361763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183281742807464562018241175 274922614211196843027361763)
  ·
    refine ⟨412383921316795264541042645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274922614211196843027361763 412383921316795264541042645)
    ·
      refine ⟨9665248155862389012680687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 412383921316795264541042645 9665248155862389012680687)
      ·
        refine ⟨14497872233793583519021031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665248155862389012680687 14497872233793583519021031)
        ·
          refine ⟨21746808350690375278531547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497872233793583519021031 21746808350690375278531547)
          ·
            refine ⟨32620212526035562917797321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21746808350690375278531547 32620212526035562917797321)
            ·
              refine ⟨24465159394526672188347991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32620212526035562917797321 24465159394526672188347991)
              ·
                refine ⟨36697739091790008282521987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24465159394526672188347991 36697739091790008282521987)
                ·
                  refine ⟨55046608637685012423782981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36697739091790008282521987 55046608637685012423782981)
                  ·
                    refine ⟨10321239119565939829459309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55046608637685012423782981 10321239119565939829459309)
                    ·
                      refine ⟨3870464669837227436047241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321239119565939829459309 3870464669837227436047241)
                      ·
                        rfl

theorem cell23_7537703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7537703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537703 prefixEnd_7537703 := by exact prefixLift 7537703
  have htrace : WordTrace (prefixWord ++ tailWord_7537703) baseStart_7537703 baseEnd_7537703 := by
    simpa [prefixWord, tailWord_7537703, baseEnd_7537703] using wordTrace_append hprefix tailTrace_7537703
  have hstable : (prefixWord ++ tailWord_7537703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537703).length < 2 ^ (prefixWord ++ tailWord_7537703).sum := by decide
  have hdescent : baseEnd_7537703 < baseStart_7537703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537719 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 5, 5]
def baseStart_7537719 : Nat := 118140960795 + 7537719 * 2 ^ 59
def prefixEnd_7537719 : Nat := 4983230072969 + 3 ^ 40 * 7537719 * 2
def baseEnd_7537719 : Nat := 1290157628509233124482389

theorem tailTrace_7537719 : CollatzResearch.WordTrace tailWord_7537719 prefixEnd_7537719 1290157628509233124482389 := by
  unfold tailWord_7537719
  simp only [CollatzResearch.WordTrace]
  refine ⟨274923197779138877759944211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183282131852759251839962807 274923197779138877759944211)
  ·
    refine ⟨412384796668708316639916317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274923197779138877759944211 412384796668708316639916317)
    ·
      refine ⟨154644298750765618739968619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412384796668708316639916317 154644298750765618739968619)
      ·
        refine ⟨231966448126148428109952929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154644298750765618739968619 231966448126148428109952929)
        ·
          refine ⟨173974836094611321082464697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231966448126148428109952929 173974836094611321082464697)
          ·
            refine ⟨130481127070958490811848523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173974836094611321082464697 130481127070958490811848523)
            ·
              refine ⟨195721690606437736217772785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130481127070958490811848523 195721690606437736217772785)
              ·
                refine ⟨146791267954828302163329589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195721690606437736217772785 146791267954828302163329589)
                ·
                  refine ⟨13761681370765153327812149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146791267954828302163329589 13761681370765153327812149)
                  ·
                    refine ⟨1290157628509233124482389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13761681370765153327812149 1290157628509233124482389)
                    ·
                      rfl

theorem cell23_7537719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_7537719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537719 prefixEnd_7537719 := by exact prefixLift 7537719
  have htrace : WordTrace (prefixWord ++ tailWord_7537719) baseStart_7537719 baseEnd_7537719 := by
    simpa [prefixWord, tailWord_7537719, baseEnd_7537719] using wordTrace_append hprefix tailTrace_7537719
  have hstable : (prefixWord ++ tailWord_7537719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537719).length < 2 ^ (prefixWord ++ tailWord_7537719).sum := by decide
  have hdescent : baseEnd_7537719 < baseStart_7537719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537733 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_7537733 : Nat := 118140960795 + 7537733 * 2 ^ 59
def prefixEnd_7537733 : Nat := 4983230072969 + 3 ^ 40 * 7537733 * 2
def baseEnd_7537733 : Nat := 3870480074256862318672103

theorem tailTrace_7537733 : CollatzResearch.WordTrace tailWord_7537733 prefixEnd_7537733 3870480074256862318672103 := by
  unfold tailWord_7537733
  simp only [CollatzResearch.WordTrace]
  refine ⟨274923708401088158150953853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183282472267392105433969235 274923708401088158150953853)
  ·
    refine ⟨103096390650408059306607695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274923708401088158150953853 103096390650408059306607695)
    ·
      refine ⟨154644585975612088959911543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103096390650408059306607695 154644585975612088959911543)
      ·
        refine ⟨231966878963418133439867315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154644585975612088959911543 231966878963418133439867315)
        ·
          refine ⟨347950318445127200159800973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231966878963418133439867315 347950318445127200159800973)
          ·
            refine ⟨130481369416922700059925365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347950318445127200159800973 130481369416922700059925365)
            ·
              refine ⟨12232628382836503130618003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130481369416922700059925365 12232628382836503130618003)
              ·
                refine ⟨18348942574254754695927005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12232628382836503130618003 18348942574254754695927005)
                ·
                  refine ⟨6880853465345533010972627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18348942574254754695927005 6880853465345533010972627)
                  ·
                    refine ⟨10321280198018299516458941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6880853465345533010972627 10321280198018299516458941)
                    ·
                      refine ⟨3870480074256862318672103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321280198018299516458941 3870480074256862318672103)
                      ·
                        rfl

theorem cell23_7537733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_7537733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537733 prefixEnd_7537733 := by exact prefixLift 7537733
  have htrace : WordTrace (prefixWord ++ tailWord_7537733) baseStart_7537733 baseEnd_7537733 := by
    simpa [prefixWord, tailWord_7537733, baseEnd_7537733] using wordTrace_append hprefix tailTrace_7537733
  have hstable : (prefixWord ++ tailWord_7537733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537733).length < 2 ^ (prefixWord ++ tailWord_7537733).sum := by decide
  have hdescent : baseEnd_7537733 < baseStart_7537733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537770 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_7537770 : Nat := 118140960795 + 7537770 * 2 ^ 59
def prefixEnd_7537770 : Nat := 4983230072969 + 3 ^ 40 * 7537770 * 2
def baseEnd_7537770 : Nat := 1290166357680359557969811

theorem tailTrace_7537770 : CollatzResearch.WordTrace tailWord_7537770 prefixEnd_7537770 1290166357680359557969811 := by
  unfold tailWord_7537770
  simp only [CollatzResearch.WordTrace]
  refine ⟨68731264475488528367512691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183283371934636075646700509 68731264475488528367512691)
  ·
    refine ⟨103096896713232792551269037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68731264475488528367512691 103096896713232792551269037)
    ·
      refine ⟨38661336267462297206725889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103096896713232792551269037 38661336267462297206725889)
      ·
        refine ⟨28996002200596722905044417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38661336267462297206725889 28996002200596722905044417)
        ·
          refine ⟨21747001650447542178783313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28996002200596722905044417 21747001650447542178783313)
          ·
            refine ⟨16310251237835656634087485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21747001650447542178783313 16310251237835656634087485)
            ·
              refine ⟨6116344214188371237782807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16310251237835656634087485 6116344214188371237782807)
              ·
                refine ⟨9174516321282556856674211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6116344214188371237782807 9174516321282556856674211)
                ·
                  refine ⟨13761774481923835285011317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9174516321282556856674211 13761774481923835285011317)
                  ·
                    refine ⟨1290166357680359557969811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13761774481923835285011317 1290166357680359557969811)
                    ·
                      rfl

theorem cell23_7537770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_7537770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537770 prefixEnd_7537770 := by exact prefixLift 7537770
  have htrace : WordTrace (prefixWord ++ tailWord_7537770) baseStart_7537770 baseEnd_7537770 := by
    simpa [prefixWord, tailWord_7537770, baseEnd_7537770] using wordTrace_append hprefix tailTrace_7537770
  have hstable : (prefixWord ++ tailWord_7537770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537770).length < 2 ^ (prefixWord ++ tailWord_7537770).sum := by decide
  have hdescent : baseEnd_7537770 < baseStart_7537770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537783 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 2, 4]
def baseStart_7537783 : Nat := 118140960795 + 7537783 * 2 ^ 59
def prefixEnd_7537783 : Nat := 4983230072969 + 3 ^ 40 * 7537783 * 2
def baseEnd_7537783 : Nat := 1290168582763195707682291

theorem tailTrace_7537783 : CollatzResearch.WordTrace tailWord_7537783 prefixEnd_7537783 1290168582763195707682291 := by
  unfold tailWord_7537783
  simp only [CollatzResearch.WordTrace]
  refine ⟨274925532050907016690274003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183283688033938011126849335 274925532050907016690274003)
  ·
    refine ⟨412388298076360525035411005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274925532050907016690274003 412388298076360525035411005)
    ·
      refine ⟨154645611778635196888279127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412388298076360525035411005 154645611778635196888279127)
      ·
        refine ⟨231968417667952795332418691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154645611778635196888279127 231968417667952795332418691)
        ·
          refine ⟨347952626501929192998628037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231968417667952795332418691 347952626501929192998628037)
          ·
            refine ⟨65241117469111723687242757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347952626501929192998628037 65241117469111723687242757)
            ·
              refine ⟨12232709525458448191358017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65241117469111723687242757 12232709525458448191358017)
              ·
                refine ⟨9174532144093836143518513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12232709525458448191358017 9174532144093836143518513)
                ·
                  refine ⟨6880899108070377107638885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9174532144093836143518513 6880899108070377107638885)
                  ·
                    refine ⟨1290168582763195707682291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880899108070377107638885 1290168582763195707682291)
                    ·
                      rfl

theorem cell23_7537783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_7537783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537783 prefixEnd_7537783 := by exact prefixLift 7537783
  have htrace : WordTrace (prefixWord ++ tailWord_7537783) baseStart_7537783 baseEnd_7537783 := by
    simpa [prefixWord, tailWord_7537783, baseEnd_7537783] using wordTrace_append hprefix tailTrace_7537783
  have hstable : (prefixWord ++ tailWord_7537783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537783).length < 2 ^ (prefixWord ++ tailWord_7537783).sum := by decide
  have hdescent : baseEnd_7537783 < baseStart_7537783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537793 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_7537793 : Nat := 118140960795 + 7537793 * 2 ^ 59
def prefixEnd_7537793 : Nat := 4983230072969 + 3 ^ 40 * 7537793 * 2
def baseEnd_7537793 : Nat := 3870510883096132083921827

theorem tailTrace_7537793 : CollatzResearch.WordTrace tailWord_7537793 prefixEnd_7537793 3870510883096132083921827 := by
  unfold tailWord_7537793
  simp only [CollatzResearch.WordTrace]
  refine ⟨274925896780870788398138033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183283931187247192265425355 274925896780870788398138033)
  ·
    refine ⟨206194422585653091298603525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274925896780870788398138033 206194422585653091298603525)
    ·
      refine ⟨38661454234809954618488161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206194422585653091298603525 38661454234809954618488161)
      ·
        refine ⟨28996090676107465963866121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38661454234809954618488161 28996090676107465963866121)
        ·
          refine ⟨21747068007080599472899591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28996090676107465963866121 21747068007080599472899591)
          ·
            refine ⟨32620602010620899209349387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21747068007080599472899591 32620602010620899209349387)
            ·
              refine ⟨48930903015931348814024081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32620602010620899209349387 48930903015931348814024081)
              ·
                refine ⟨36698177261948511610518061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48930903015931348814024081 36698177261948511610518061)
                ·
                  refine ⟨13761816473230691853944273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36698177261948511610518061 13761816473230691853944273)
                  ·
                    refine ⟨10321362354923018890458205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13761816473230691853944273 10321362354923018890458205)
                    ·
                      refine ⟨3870510883096132083921827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321362354923018890458205 3870510883096132083921827)
                      ·
                        rfl

theorem cell23_7537793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_7537793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537793 prefixEnd_7537793 := by exact prefixLift 7537793
  have htrace : WordTrace (prefixWord ++ tailWord_7537793) baseStart_7537793 baseEnd_7537793 := by
    simpa [prefixWord, tailWord_7537793, baseEnd_7537793] using wordTrace_append hprefix tailTrace_7537793
  have hstable : (prefixWord ++ tailWord_7537793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537793).length < 2 ^ (prefixWord ++ tailWord_7537793).sum := by decide
  have hdescent : baseEnd_7537793 < baseStart_7537793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537796 : List Nat := [2, 3, 2, 1, 2, 2, 3, 8]
def baseStart_7537796 : Nat := 118140960795 + 7537796 * 2 ^ 59
def prefixEnd_7537796 : Nat := 4983230072969 + 3 ^ 40 * 7537796 * 2
def baseEnd_7537796 : Nat := 143352311982892428599419

theorem tailTrace_7537796 : CollatzResearch.WordTrace tailWord_7537796 prefixEnd_7537796 143352311982892428599419 := by
  unfold tailWord_7537796
  simp only [CollatzResearch.WordTrace]
  refine ⟨137463003099929959955248621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183284004133239946606998161 137463003099929959955248621)
  ·
    refine ⟨51548626162473734983218233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137463003099929959955248621 51548626162473734983218233)
    ·
      refine ⟨38661469621855301237413675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51548626162473734983218233 38661469621855301237413675)
      ·
        refine ⟨57992204432782951856120513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38661469621855301237413675 57992204432782951856120513)
        ·
          refine ⟨43494153324587213892090385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57992204432782951856120513 43494153324587213892090385)
          ·
            refine ⟨32620614993440410419067789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43494153324587213892090385 32620614993440410419067789)
            ·
              refine ⟨12232730622540153907150421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32620614993440410419067789 12232730622540153907150421)
              ·
                refine ⟨143352311982892428599419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12232730622540153907150421 143352311982892428599419)
                ·
                  rfl

theorem cell23_7537796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 8].length) (baseStart_7537796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537796 prefixEnd_7537796 := by exact prefixLift 7537796
  have htrace : WordTrace (prefixWord ++ tailWord_7537796) baseStart_7537796 baseEnd_7537796 := by
    simpa [prefixWord, tailWord_7537796, baseEnd_7537796] using wordTrace_append hprefix tailTrace_7537796
  have hstable : (prefixWord ++ tailWord_7537796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537796).length < 2 ^ (prefixWord ++ tailWord_7537796).sum := by decide
  have hdescent : baseEnd_7537796 < baseStart_7537796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537857 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7537857 : Nat := 118140960795 + 7537857 * 2 ^ 59
def prefixEnd_7537857 : Nat := 4983230072969 + 3 ^ 40 * 7537857 * 2
def baseEnd_7537857 : Nat := 3870543745858019833521533

theorem tailTrace_7537857 : CollatzResearch.WordTrace tailWord_7537857 prefixEnd_7537857 3870543745858019833521533 := by
  unfold tailWord_7537857
  simp only [CollatzResearch.WordTrace]
  refine ⟨274928231052638927328467825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183285487368425951552311883 274928231052638927328467825)
  ·
    refine ⟨206196173289479195496350869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274928231052638927328467825 206196173289479195496350869)
    ·
      refine ⟨9665445622944337288891447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206196173289479195496350869 9665445622944337288891447)
      ·
        refine ⟨14498168434416505933337171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665445622944337288891447 14498168434416505933337171)
        ·
          refine ⟨21747252651624758900005757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14498168434416505933337171 21747252651624758900005757)
          ·
            refine ⟨8155219744359284587502159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21747252651624758900005757 8155219744359284587502159)
            ·
              refine ⟨12232829616538926881253239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8155219744359284587502159 12232829616538926881253239)
              ·
                refine ⟨18349244424808390321879859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12232829616538926881253239 18349244424808390321879859)
                ·
                  refine ⟨27523866637212585482819789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18349244424808390321879859 27523866637212585482819789)
                  ·
                    refine ⟨10321449988954719556057421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27523866637212585482819789 10321449988954719556057421)
                    ·
                      refine ⟨3870543745858019833521533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321449988954719556057421 3870543745858019833521533)
                      ·
                        rfl

theorem cell23_7537857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7537857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537857 prefixEnd_7537857 := by exact prefixLift 7537857
  have htrace : WordTrace (prefixWord ++ tailWord_7537857) baseStart_7537857 baseEnd_7537857 := by
    simpa [prefixWord, tailWord_7537857, baseEnd_7537857] using wordTrace_append hprefix tailTrace_7537857
  have hstable : (prefixWord ++ tailWord_7537857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537857).length < 2 ^ (prefixWord ++ tailWord_7537857).sum := by decide
  have hdescent : baseEnd_7537857 < baseStart_7537857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537896 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7537896 : Nat := 118140960795 + 7537896 * 2 ^ 59
def prefixEnd_7537896 : Nat := 4983230072969 + 3 ^ 40 * 7537896 * 2
def baseEnd_7537896 : Nat := 3870563771603545180933853

theorem tailTrace_7537896 : CollatzResearch.WordTrace tailWord_7537896 prefixEnd_7537896 3870563771603545180933853 := by
  unfold tailWord_7537896
  simp only [CollatzResearch.WordTrace]
  refine ⟨137464826749748818494568771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183286435666331757992758361 137464826749748818494568771)
  ·
    refine ⟨206197240124623227741853157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137464826749748818494568771 206197240124623227741853157)
    ·
      refine ⟨38661982523366855201597467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206197240124623227741853157 38661982523366855201597467)
      ·
        refine ⟨57992973785050282802396201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38661982523366855201597467 57992973785050282802396201)
        ·
          refine ⟨43494730338787712101797151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57992973785050282802396201 43494730338787712101797151)
          ·
            refine ⟨65242095508181568152695727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43494730338787712101797151 65242095508181568152695727)
            ·
              refine ⟨97863143262272352229043591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65242095508181568152695727 97863143262272352229043591)
              ·
                refine ⟨146794714893408528343565387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97863143262272352229043591 146794714893408528343565387)
                ·
                  refine ⟨220192072340112792515348081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146794714893408528343565387 220192072340112792515348081)
                  ·
                    refine ⟨165144054255084594386511061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220192072340112792515348081 165144054255084594386511061)
                    ·
                      refine ⟨3870563771603545180933853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165144054255084594386511061 3870563771603545180933853)
                      ·
                        rfl

theorem cell23_7537896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7537896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537896 prefixEnd_7537896 := by exact prefixLift 7537896
  have htrace : WordTrace (prefixWord ++ tailWord_7537896) baseStart_7537896 baseEnd_7537896 := by
    simpa [prefixWord, tailWord_7537896, baseEnd_7537896] using wordTrace_append hprefix tailTrace_7537896
  have hstable : (prefixWord ++ tailWord_7537896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537896).length < 2 ^ (prefixWord ++ tailWord_7537896).sum := by decide
  have hdescent : baseEnd_7537896 < baseStart_7537896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537936 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_7537936 : Nat := 118140960795 + 7537936 * 2 ^ 59
def prefixEnd_7537936 : Nat := 4983230072969 + 3 ^ 40 * 7537936 * 2
def baseEnd_7537936 : Nat := 3870584310829725024433669

theorem tailTrace_7537936 : CollatzResearch.WordTrace tailWord_7537936 prefixEnd_7537936 3870584310829725024433669 := by
  unfold tailWord_7537936
  simp only [CollatzResearch.WordTrace]
  refine ⟨137465556209676361910296831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183287408279568482547062441 137465556209676361910296831)
  ·
    refine ⟨206198334314514542865445247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137465556209676361910296831 206198334314514542865445247)
    ·
      refine ⟨309297501471771814298167871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206198334314514542865445247 309297501471771814298167871)
      ·
        refine ⟨463946252207657721447251807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309297501471771814298167871 463946252207657721447251807)
        ·
          refine ⟨695919378311486582170877711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463946252207657721447251807 695919378311486582170877711)
          ·
            refine ⟨1043879067467229873256316567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695919378311486582170877711 1043879067467229873256316567)
            ·
              refine ⟨1565818601200844809884474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043879067467229873256316567 1565818601200844809884474851)
              ·
                refine ⟨2348727901801267214826712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1565818601200844809884474851 2348727901801267214826712277)
                ·
                  refine ⟨55048310198467200347501069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2348727901801267214826712277 55048310198467200347501069)
                  ·
                    refine ⟨20643116324425200130312901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55048310198467200347501069 20643116324425200130312901)
                    ·
                      refine ⟨3870584310829725024433669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20643116324425200130312901 3870584310829725024433669)
                      ·
                        rfl

theorem cell23_7537936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_7537936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537936 prefixEnd_7537936 := by exact prefixLift 7537936
  have htrace : WordTrace (prefixWord ++ tailWord_7537936) baseStart_7537936 baseEnd_7537936 := by
    simpa [prefixWord, tailWord_7537936, baseEnd_7537936] using wordTrace_append hprefix tailTrace_7537936
  have hstable : (prefixWord ++ tailWord_7537936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537936).length < 2 ^ (prefixWord ++ tailWord_7537936).sum := by decide
  have hdescent : baseEnd_7537936 < baseStart_7537936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537954 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_7537954 : Nat := 118140960795 + 7537954 * 2 ^ 59
def prefixEnd_7537954 : Nat := 4983230072969 + 3 ^ 40 * 7537954 * 2
def baseEnd_7537954 : Nat := 430065950386833994889843

theorem tailTrace_7537954 : CollatzResearch.WordTrace tailWord_7537954 prefixEnd_7537954 430065950386833994889843 := by
  unfold tailWord_7537954
  simp only [CollatzResearch.WordTrace]
  refine ⟨68732942233321878223687229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183287845955525008596499277 68732942233321878223687229)
  ·
    refine ⟨25774853337495704333882711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68732942233321878223687229 25774853337495704333882711)
    ·
      refine ⟨38662280006243556500824067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774853337495704333882711 38662280006243556500824067)
      ·
        refine ⟨57993420009365334751236101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38662280006243556500824067 57993420009365334751236101)
        ·
          refine ⟨10873766251756000265856769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57993420009365334751236101 10873766251756000265856769)
          ·
            refine ⟨8155324688817000199392577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10873766251756000265856769 8155324688817000199392577)
            ·
              refine ⟨6116493516612750149544433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8155324688817000199392577 6116493516612750149544433)
              ·
                refine ⟨4587370137459562612158325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116493516612750149544433 4587370137459562612158325)
                ·
                  refine ⟨430065950386833994889843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4587370137459562612158325 430065950386833994889843)
                  ·
                    rfl

theorem cell23_7537954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_7537954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537954 prefixEnd_7537954 := by exact prefixLift 7537954
  have htrace : WordTrace (prefixWord ++ tailWord_7537954) baseStart_7537954 baseEnd_7537954 := by
    simpa [prefixWord, tailWord_7537954, baseEnd_7537954] using wordTrace_append hprefix tailTrace_7537954
  have hstable : (prefixWord ++ tailWord_7537954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537954).length < 2 ^ (prefixWord ++ tailWord_7537954).sum := by decide
  have hdescent : baseEnd_7537954 < baseStart_7537954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537970 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_7537970 : Nat := 118140960795 + 7537970 * 2 ^ 59
def prefixEnd_7537970 : Nat := 4983230072969 + 3 ^ 40 * 7537970 * 2
def baseEnd_7537970 : Nat := 3870601769171977891408513

theorem tailTrace_7537970 : CollatzResearch.WordTrace tailWord_7537970 prefixEnd_7537970 3870601769171977891408513 := by
  unfold tailWord_7537970
  simp only [CollatzResearch.WordTrace]
  refine ⟨68733088125307386906832841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183288235000819698418220909 68733088125307386906832841)
  ·
    refine ⟨51549816093980540180124631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68733088125307386906832841 51549816093980540180124631)
    ·
      refine ⟨77324724140970810270186947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51549816093980540180124631 77324724140970810270186947)
      ·
        refine ⟨115987086211456215405280421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77324724140970810270186947 115987086211456215405280421)
        ·
          refine ⟨21747578664648040388490079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115987086211456215405280421 21747578664648040388490079)
          ·
            refine ⟨32621367996972060582735119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21747578664648040388490079 32621367996972060582735119)
            ·
              refine ⟨48932051995458090874102679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32621367996972060582735119 48932051995458090874102679)
              ·
                refine ⟨73398077993187136311154019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48932051995458090874102679 73398077993187136311154019)
                ·
                  refine ⟨110097116989780704466731029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73398077993187136311154019 110097116989780704466731029)
                  ·
                    refine ⟨5160802358895970521878017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110097116989780704466731029 5160802358895970521878017)
                    ·
                      refine ⟨3870601769171977891408513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160802358895970521878017 3870601769171977891408513)
                      ·
                        rfl

theorem cell23_7537970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_7537970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537970 prefixEnd_7537970 := by exact prefixLift 7537970
  have htrace : WordTrace (prefixWord ++ tailWord_7537970) baseStart_7537970 baseEnd_7537970 := by
    simpa [prefixWord, tailWord_7537970, baseEnd_7537970] using wordTrace_append hprefix tailTrace_7537970
  have hstable : (prefixWord ++ tailWord_7537970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537970).length < 2 ^ (prefixWord ++ tailWord_7537970).sum := by decide
  have hdescent : baseEnd_7537970 < baseStart_7537970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537976 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 10]
def baseStart_7537976 : Nat := 118140960795 + 7537976 * 2 ^ 59
def prefixEnd_7537976 : Nat := 4983230072969 + 3 ^ 40 * 7537976 * 2
def baseEnd_7537976 : Nat := 430067205561767207548165

theorem tailTrace_7537976 : CollatzResearch.WordTrace tailWord_7537976 prefixEnd_7537976 430067205561767207548165 := by
  unfold tailWord_7537976
  simp only [CollatzResearch.WordTrace]
  refine ⟨137466285669603905326024891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183288380892805207101366521 137466285669603905326024891)
  ·
    refine ⟨206199428504405857989037337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137466285669603905326024891 206199428504405857989037337)
    ·
      refine ⟨154649571378304393491778003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206199428504405857989037337 154649571378304393491778003)
      ·
        refine ⟨231974357067456590237667005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154649571378304393491778003 231974357067456590237667005)
        ·
          refine ⟨86990383900296221339125127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231974357067456590237667005 86990383900296221339125127)
          ·
            refine ⟨130485575850444332008687691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86990383900296221339125127 130485575850444332008687691)
            ·
              refine ⟨195728363775666498013031537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130485575850444332008687691 195728363775666498013031537)
              ·
                refine ⟨146796272831749873509773653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195728363775666498013031537 146796272831749873509773653)
                ·
                  refine ⟨430067205561767207548165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 146796272831749873509773653 430067205561767207548165)
                  ·
                    rfl

theorem cell23_7537976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_7537976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537976 prefixEnd_7537976 := by exact prefixLift 7537976
  have htrace : WordTrace (prefixWord ++ tailWord_7537976) baseStart_7537976 baseEnd_7537976 := by
    simpa [prefixWord, tailWord_7537976, baseEnd_7537976] using wordTrace_append hprefix tailTrace_7537976
  have hstable : (prefixWord ++ tailWord_7537976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537976).length < 2 ^ (prefixWord ++ tailWord_7537976).sum := by decide
  have hdescent : baseEnd_7537976 < baseStart_7537976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7537980 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_7537980 : Nat := 118140960795 + 7537980 * 2 ^ 59
def prefixEnd_7537980 : Nat := 4983230072969 + 3 ^ 40 * 7537980 * 2
def baseEnd_7537980 : Nat := 1290202301326174284094489

theorem tailTrace_7537980 : CollatzResearch.WordTrace tailWord_7537980 prefixEnd_7537980 1290202301326174284094489 := by
  unfold tailWord_7537980
  simp only [CollatzResearch.WordTrace]
  refine ⟨137466358615596659667597697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183288478154128879556796929 137466358615596659667597697)
  ·
    refine ⟨103099768961697494750698273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137466358615596659667597697 103099768961697494750698273)
    ·
      refine ⟨77324826721273121063023705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103099768961697494750698273 77324826721273121063023705)
      ·
        refine ⟨57993620040954840797267779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77324826721273121063023705 57993620040954840797267779)
        ·
          refine ⟨86990430061432261195901669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57993620040954840797267779 86990430061432261195901669)
          ·
            refine ⟨16310705636518548974231563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86990430061432261195901669 16310705636518548974231563)
            ·
              refine ⟨24466058454777823461347345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16310705636518548974231563 24466058454777823461347345)
              ·
                refine ⟨18349543841083367596010509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24466058454777823461347345 18349543841083367596010509)
                ·
                  refine ⟨6881078940406262848503941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18349543841083367596010509 6881078940406262848503941)
                  ·
                    refine ⟨1290202301326174284094489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881078940406262848503941 1290202301326174284094489)
                    ·
                      rfl

theorem cell23_7537980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_7537980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7537980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7537980 prefixEnd_7537980 := by exact prefixLift 7537980
  have htrace : WordTrace (prefixWord ++ tailWord_7537980) baseStart_7537980 baseEnd_7537980 := by
    simpa [prefixWord, tailWord_7537980, baseEnd_7537980] using wordTrace_append hprefix tailTrace_7537980
  have hstable : (prefixWord ++ tailWord_7537980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7537980).length < 2 ^ (prefixWord ++ tailWord_7537980).sum := by decide
  have hdescent : baseEnd_7537980 < baseStart_7537980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7537980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538053 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_7538053 : Nat := 118140960795 + 7538053 * 2 ^ 59
def prefixEnd_7538053 : Nat := 4983230072969 + 3 ^ 40 * 7538053 * 2
def baseEnd_7538053 : Nat := 1290214796022100355556877

theorem tailTrace_7538053 : CollatzResearch.WordTrace tailWord_7538053 prefixEnd_7538053 1290214796022100355556877 := by
  unfold tailWord_7538053
  simp only [CollatzResearch.WordTrace]
  refine ⟨274935379759928852802602813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183290253173285901868401875 274935379759928852802602813)
  ·
    refine ⟨103100767409973319800976055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274935379759928852802602813 103100767409973319800976055)
    ·
      refine ⟨154651151114959979701464083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103100767409973319800976055 154651151114959979701464083)
      ·
        refine ⟨231976726672439969552196125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154651151114959979701464083 231976726672439969552196125)
        ·
          refine ⟨86991272502164988582073547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231976726672439969552196125 86991272502164988582073547)
          ·
            refine ⟨130486908753247482873110321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86991272502164988582073547 130486908753247482873110321)
            ·
              refine ⟨97865181564935612154832741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130486908753247482873110321 97865181564935612154832741)
              ·
                refine ⟨18349721543425427279031139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97865181564935612154832741 18349721543425427279031139)
                ·
                  refine ⟨27524582315138140918546709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18349721543425427279031139 27524582315138140918546709)
                  ·
                    refine ⟨1290214796022100355556877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27524582315138140918546709 1290214796022100355556877)
                    ·
                      rfl

theorem cell23_7538053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_7538053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538053 prefixEnd_7538053 := by exact prefixLift 7538053
  have htrace : WordTrace (prefixWord ++ tailWord_7538053) baseStart_7538053 baseEnd_7538053 := by
    simpa [prefixWord, tailWord_7538053, baseEnd_7538053] using wordTrace_append hprefix tailTrace_7538053
  have hstable : (prefixWord ++ tailWord_7538053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538053).length < 2 ^ (prefixWord ++ tailWord_7538053).sum := by decide
  have hdescent : baseEnd_7538053 < baseStart_7538053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538060 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 1, 1, 4]
def baseStart_7538060 : Nat := 118140960795 + 7538060 * 2 ^ 59
def prefixEnd_7538060 : Nat := 4983230072969 + 3 ^ 40 * 7538060 * 2
def baseEnd_7538060 : Nat := 3870647982430882539283099

theorem tailTrace_7538060 : CollatzResearch.WordTrace tailWord_7538060 prefixEnd_7538060 3870647982430882539283099 := by
  unfold tailWord_7538060
  simp only [CollatzResearch.WordTrace]
  refine ⟨137467817535451746499053817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183290423380602328665405089 137467817535451746499053817)
  ·
    refine ⟨103100863151588809874290363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137467817535451746499053817 103100863151588809874290363)
    ·
      refine ⟨154651294727383214811435545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103100863151588809874290363 154651294727383214811435545)
      ·
        refine ⟨115988471045537411108576659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154651294727383214811435545 115988471045537411108576659)
        ·
          refine ⟨173982706568306116662864989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115988471045537411108576659 173982706568306116662864989)
          ·
            refine ⟨65243514963114793748574371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173982706568306116662864989 65243514963114793748574371)
            ·
              refine ⟨97865272444672190622861557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65243514963114793748574371 97865272444672190622861557)
              ·
                refine ⟨9174869291688017870893271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97865272444672190622861557 9174869291688017870893271)
                ·
                  refine ⟨13762303937532026806339907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9174869291688017870893271 13762303937532026806339907)
                  ·
                    refine ⟨20643455906298040209509861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13762303937532026806339907 20643455906298040209509861)
                    ·
                      refine ⟨3870647982430882539283099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20643455906298040209509861 3870647982430882539283099)
                      ·
                        rfl

theorem cell23_7538060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_7538060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538060 prefixEnd_7538060 := by exact prefixLift 7538060
  have htrace : WordTrace (prefixWord ++ tailWord_7538060) baseStart_7538060 baseEnd_7538060 := by
    simpa [prefixWord, tailWord_7538060, baseEnd_7538060] using wordTrace_append hprefix tailTrace_7538060
  have hstable : (prefixWord ++ tailWord_7538060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538060).length < 2 ^ (prefixWord ++ tailWord_7538060).sum := by decide
  have hdescent : baseEnd_7538060 < baseStart_7538060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538073 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_7538073 : Nat := 118140960795 + 7538073 * 2 ^ 59
def prefixEnd_7538073 : Nat := 4983230072969 + 3 ^ 40 * 7538073 * 2
def baseEnd_7538073 : Nat := 3870654657679390988420539

theorem tailTrace_7538073 : CollatzResearch.WordTrace tailWord_7538073 prefixEnd_7538073 3870654657679390988420539 := by
  unfold tailWord_7538073
  simp only [CollatzResearch.WordTrace]
  refine ⟨274936109219856396218330873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183290739479904264145553915 274936109219856396218330873)
  ·
    refine ⟨206202081914892297163748155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274936109219856396218330873 206202081914892297163748155)
    ·
      refine ⟨309303122872338445745622233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206202081914892297163748155 309303122872338445745622233)
      ·
        refine ⟨231977342154253834309216675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309303122872338445745622233 231977342154253834309216675)
        ·
          refine ⟨347966013231380751463825013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231977342154253834309216675 347966013231380751463825013)
          ·
            refine ⟨32621813740441945449733595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347966013231380751463825013 32621813740441945449733595)
            ·
              refine ⟨48932720610662918174600393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32621813740441945449733595 48932720610662918174600393)
              ·
                refine ⟨36699540457997188630950295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48932720610662918174600393 36699540457997188630950295)
                ·
                  refine ⟨55049310686995782946425443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36699540457997188630950295 55049310686995782946425443)
                  ·
                    refine ⟨82573966030493674419638165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55049310686995782946425443 82573966030493674419638165)
                    ·
                      refine ⟨3870654657679390988420539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82573966030493674419638165 3870654657679390988420539)
                      ·
                        rfl

theorem cell23_7538073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_7538073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538073 prefixEnd_7538073 := by exact prefixLift 7538073
  have htrace : WordTrace (prefixWord ++ tailWord_7538073) baseStart_7538073 baseEnd_7538073 := by
    simpa [prefixWord, tailWord_7538073, baseEnd_7538073] using wordTrace_append hprefix tailTrace_7538073
  have hstable : (prefixWord ++ tailWord_7538073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538073).length < 2 ^ (prefixWord ++ tailWord_7538073).sum := by decide
  have hdescent : baseEnd_7538073 < baseStart_7538073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538080 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_7538080 : Nat := 118140960795 + 7538080 * 2 ^ 59
def prefixEnd_7538080 : Nat := 4983230072969 + 3 ^ 40 * 7538080 * 2
def baseEnd_7538080 : Nat := 3870658252043972461033007

theorem tailTrace_7538080 : CollatzResearch.WordTrace tailWord_7538080 prefixEnd_7538080 3870658252043972461033007 := by
  unfold tailWord_7538080
  simp only [CollatzResearch.WordTrace]
  refine ⟨137468182265415518206917847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183290909687220690942557129 137468182265415518206917847)
  ·
    refine ⟨206202273398123277310376771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137468182265415518206917847 206202273398123277310376771)
    ·
      refine ⟨309303410097184915965565157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206202273398123277310376771 309303410097184915965565157)
      ·
        refine ⟨57994389393222171743543467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309303410097184915965565157 57994389393222171743543467)
        ·
          refine ⟨86991584089833257615315201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57994389393222171743543467 86991584089833257615315201)
          ·
            refine ⟨65243688067374943211486401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86991584089833257615315201 65243688067374943211486401)
            ·
              refine ⟨48932766050531207408614801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65243688067374943211486401 48932766050531207408614801)
              ·
                refine ⟨36699574537898405556461101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48932766050531207408614801 36699574537898405556461101)
                ·
                  refine ⟨13762340451711902083672913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36699574537898405556461101 13762340451711902083672913)
                  ·
                    refine ⟨10321755338783926562754685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13762340451711902083672913 10321755338783926562754685)
                    ·
                      refine ⟨3870658252043972461033007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321755338783926562754685 3870658252043972461033007)
                      ·
                        rfl

theorem cell23_7538080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_7538080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538080 prefixEnd_7538080 := by exact prefixLift 7538080
  have htrace : WordTrace (prefixWord ++ tailWord_7538080) baseStart_7538080 baseEnd_7538080 := by
    simpa [prefixWord, tailWord_7538080, baseEnd_7538080] using wordTrace_append hprefix tailTrace_7538080
  have hstable : (prefixWord ++ tailWord_7538080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538080).length < 2 ^ (prefixWord ++ tailWord_7538080).sum := by decide
  have hdescent : baseEnd_7538080 < baseStart_7538080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538083 : List Nat := [1, 1, 1, 4, 1, 3, 4, 8]
def baseStart_7538083 : Nat := 118140960795 + 7538083 * 2 ^ 59
def prefixEnd_7538083 : Nat := 4983230072969 + 3 ^ 40 * 7538083 * 2
def baseEnd_7538083 : Nat := 143357770092071701825759

theorem tailTrace_7538083 : CollatzResearch.WordTrace tailWord_7538083 prefixEnd_7538083 143357770092071701825759 := by
  unfold tailWord_7538083
  simp only [CollatzResearch.WordTrace]
  refine ⟨274936473949820167926194903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183290982633213445284129935 274936473949820167926194903)
  ·
    refine ⟨412404710924730251889292355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274936473949820167926194903 412404710924730251889292355)
    ·
      refine ⟨618607066387095377833938533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412404710924730251889292355 618607066387095377833938533)
      ·
        refine ⟨115988824947580383343863475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 618607066387095377833938533 115988824947580383343863475)
        ·
          refine ⟨173983237421370575015795213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115988824947580383343863475 173983237421370575015795213)
          ·
            refine ⟨65243714033013965630923205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173983237421370575015795213 65243714033013965630923205)
            ·
              refine ⟨12233196381190118555798101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65243714033013965630923205 12233196381190118555798101)
              ·
                refine ⟨143357770092071701825759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12233196381190118555798101 143357770092071701825759)
                ·
                  rfl

theorem cell23_7538083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 8].length) (baseStart_7538083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538083 prefixEnd_7538083 := by exact prefixLift 7538083
  have htrace : WordTrace (prefixWord ++ tailWord_7538083) baseStart_7538083 baseEnd_7538083 := by
    simpa [prefixWord, tailWord_7538083, baseEnd_7538083] using wordTrace_append hprefix tailTrace_7538083
  have hstable : (prefixWord ++ tailWord_7538083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538083).length < 2 ^ (prefixWord ++ tailWord_7538083).sum := by decide
  have hdescent : baseEnd_7538083 < baseStart_7538083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538087 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7538087 : Nat := 118140960795 + 7538087 * 2 ^ 59
def prefixEnd_7538087 : Nat := 4983230072969 + 3 ^ 40 * 7538087 * 2
def baseEnd_7538087 : Nat := 1290220615469517977881825

theorem tailTrace_7538087 : CollatzResearch.WordTrace tailWord_7538087 prefixEnd_7538087 1290220615469517977881825 := by
  unfold tailWord_7538087
  simp only [CollatzResearch.WordTrace]
  refine ⟨274936619841805676609340515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183291079894537117739560343 274936619841805676609340515)
  ·
    refine ⟨412404929762708514914010773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274936619841805676609340515 412404929762708514914010773)
    ·
      refine ⟨19331481082626961636594255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 412404929762708514914010773 19331481082626961636594255)
      ·
        refine ⟨28997221623940442454891383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19331481082626961636594255 28997221623940442454891383)
        ·
          refine ⟨43495832435910663682337075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28997221623940442454891383 43495832435910663682337075)
          ·
            refine ⟨65243748653865995523505613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43495832435910663682337075 65243748653865995523505613)
            ·
              refine ⟨24466405745199748321314605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65243748653865995523505613 24466405745199748321314605)
              ·
                refine ⟨9174902154449905620492977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24466405745199748321314605 9174902154449905620492977)
                ·
                  refine ⟨6881176615837429215369733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9174902154449905620492977 6881176615837429215369733)
                  ·
                    refine ⟨1290220615469517977881825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881176615837429215369733 1290220615469517977881825)
                    ·
                      rfl

theorem cell23_7538087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7538087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538087 prefixEnd_7538087 := by exact prefixLift 7538087
  have htrace : WordTrace (prefixWord ++ tailWord_7538087) baseStart_7538087 baseEnd_7538087 := by
    simpa [prefixWord, tailWord_7538087, baseEnd_7538087] using wordTrace_append hprefix tailTrace_7538087
  have hstable : (prefixWord ++ tailWord_7538087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538087).length < 2 ^ (prefixWord ++ tailWord_7538087).sum := by decide
  have hdescent : baseEnd_7538087 < baseStart_7538087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538123 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_7538123 : Nat := 118140960795 + 7538123 * 2 ^ 59
def prefixEnd_7538123 : Nat := 4983230072969 + 3 ^ 40 * 7538123 * 2
def baseEnd_7538123 : Nat := 3870680331712115792795309

theorem tailTrace_7538123 : CollatzResearch.WordTrace tailWord_7538123 prefixEnd_7538123 3870680331712115792795309 := by
  unfold tailWord_7538123
  simp only [CollatzResearch.WordTrace]
  refine ⟨274937932869675254757651023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183291955246450169838434015 274937932869675254757651023)
  ·
    refine ⟨412406899304512882136476535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274937932869675254757651023 412406899304512882136476535)
    ·
      refine ⟨618610348956769323204714803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412406899304512882136476535 618610348956769323204714803)
      ·
        refine ⟨927915523435153984807072205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618610348956769323204714803 927915523435153984807072205)
        ·
          refine ⟨347968321288182744302652077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927915523435153984807072205 347968321288182744302652077)
          ·
            refine ⟨130488120483068529113494529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347968321288182744302652077 130488120483068529113494529)
            ·
              refine ⟨97866090362301396835120897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130488120483068529113494529 97866090362301396835120897)
              ·
                refine ⟨73399567771726047626340673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97866090362301396835120897 73399567771726047626340673)
                ·
                  refine ⟨55049675828794535719755505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73399567771726047626340673 55049675828794535719755505)
                  ·
                    refine ⟨41287256871595901789816629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55049675828794535719755505 41287256871595901789816629)
                    ·
                      refine ⟨3870680331712115792795309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41287256871595901789816629 3870680331712115792795309)
                      ·
                        rfl

theorem cell23_7538123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_7538123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538123 prefixEnd_7538123 := by exact prefixLift 7538123
  have htrace : WordTrace (prefixWord ++ tailWord_7538123) baseStart_7538123 baseEnd_7538123 := by
    simpa [prefixWord, tailWord_7538123, baseEnd_7538123] using wordTrace_append hprefix tailTrace_7538123
  have hstable : (prefixWord ++ tailWord_7538123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538123).length < 2 ^ (prefixWord ++ tailWord_7538123).sum := by decide
  have hdescent : baseEnd_7538123 < baseStart_7538123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538127 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 3]
def baseStart_7538127 : Nat := 118140960795 + 7538127 * 2 ^ 59
def prefixEnd_7538127 : Nat := 4983230072969 + 3 ^ 40 * 7538127 * 2
def baseEnd_7538127 : Nat := 3870682385634733777145291

theorem tailTrace_7538127 : CollatzResearch.WordTrace tailWord_7538127 prefixEnd_7538127 3870682385634733777145291 := by
  unfold tailWord_7538127
  simp only [CollatzResearch.WordTrace]
  refine ⟨274938078761660763440796635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183292052507773842293864423 274938078761660763440796635)
  ·
    refine ⟨412407118142491145161194953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274938078761660763440796635 412407118142491145161194953)
    ·
      refine ⟨309305338606868358870896215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412407118142491145161194953 309305338606868358870896215)
      ·
        refine ⟨463958007910302538306344323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309305338606868358870896215 463958007910302538306344323)
        ·
          refine ⟨695937011865453807459516485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463958007910302538306344323 695937011865453807459516485)
          ·
            refine ⟨130488189724772588898659341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695937011865453807459516485 130488189724772588898659341)
            ·
              refine ⟨48933071146789720836997253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130488189724772588898659341 48933071146789720836997253)
              ·
                refine ⟨9174950840023072656936985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48933071146789720836997253 9174950840023072656936985)
                ·
                  refine ⟨6881213130017304492702739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9174950840023072656936985 6881213130017304492702739)
                  ·
                    refine ⟨10321819695025956739054109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881213130017304492702739 10321819695025956739054109)
                    ·
                      refine ⟨3870682385634733777145291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321819695025956739054109 3870682385634733777145291)
                      ·
                        rfl

theorem cell23_7538127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_7538127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538127 prefixEnd_7538127 := by exact prefixLift 7538127
  have htrace : WordTrace (prefixWord ++ tailWord_7538127) baseStart_7538127 baseEnd_7538127 := by
    simpa [prefixWord, tailWord_7538127, baseEnd_7538127] using wordTrace_append hprefix tailTrace_7538127
  have hstable : (prefixWord ++ tailWord_7538127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538127).length < 2 ^ (prefixWord ++ tailWord_7538127).sum := by decide
  have hdescent : baseEnd_7538127 < baseStart_7538127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538137 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 3, 3, 2]
def baseStart_7538137 : Nat := 118140960795 + 7538137 * 2 ^ 59
def prefixEnd_7538137 : Nat := 4983230072969 + 3 ^ 40 * 7538137 * 2
def baseEnd_7538137 : Nat := 3870687520441278738020245

theorem tailTrace_7538137 : CollatzResearch.WordTrace tailWord_7538137 prefixEnd_7538137 3870687520441278738020245 := by
  unfold tailWord_7538137
  simp only [CollatzResearch.WordTrace]
  refine ⟨274938443491624535148660665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183292295661083023432440443 274938443491624535148660665)
  ·
    refine ⟨206203832618718401361495499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274938443491624535148660665 206203832618718401361495499)
    ·
      refine ⟨309305748928077602042243249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206203832618718401361495499 309305748928077602042243249)
      ·
        refine ⟨231979311696058201531682437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309305748928077602042243249 231979311696058201531682437)
        ·
          refine ⟨43496120943010912787190457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231979311696058201531682437 43496120943010912787190457)
          ·
            refine ⟨32622090707258184590392843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43496120943010912787190457 32622090707258184590392843)
            ·
              refine ⟨48933136060887276885589265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32622090707258184590392843 48933136060887276885589265)
              ·
                refine ⟨36699852045665457664191949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48933136060887276885589265 36699852045665457664191949)
                ·
                  refine ⟨13762444517124546624071981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36699852045665457664191949 13762444517124546624071981)
                  ·
                    refine ⟨5160916693921704984026993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13762444517124546624071981 5160916693921704984026993)
                    ·
                      refine ⟨3870687520441278738020245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160916693921704984026993 3870687520441278738020245)
                      ·
                        rfl

theorem cell23_7538137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_7538137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538137 prefixEnd_7538137 := by exact prefixLift 7538137
  have htrace : WordTrace (prefixWord ++ tailWord_7538137) baseStart_7538137 baseEnd_7538137 := by
    simpa [prefixWord, tailWord_7538137, baseEnd_7538137] using wordTrace_append hprefix tailTrace_7538137
  have hstable : (prefixWord ++ tailWord_7538137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538137).length < 2 ^ (prefixWord ++ tailWord_7538137).sum := by decide
  have hdescent : baseEnd_7538137 < baseStart_7538137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538178 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7538178 : Nat := 118140960795 + 7538178 * 2 ^ 59
def prefixEnd_7538178 : Nat := 4983230072969 + 3 ^ 40 * 7538178 * 2
def baseEnd_7538178 : Nat := 3870708573148113077607557

theorem tailTrace_7538178 : CollatzResearch.WordTrace tailWord_7538178 prefixEnd_7538178 3870708573148113077607557 := by
  unfold tailWord_7538178
  simp only [CollatzResearch.WordTrace]
  refine ⟨68734984721118999787725797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183293292589650666100602125 68734984721118999787725797)
  ·
    refine ⟨12887809635209812460198587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68734984721118999787725797 12887809635209812460198587)
    ·
      refine ⟨19331714452814718690297881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12887809635209812460198587 19331714452814718690297881)
      ·
        refine ⟨14498785839611039017723411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19331714452814718690297881 14498785839611039017723411)
        ·
          refine ⟨21748178759416558526585117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14498785839611039017723411 21748178759416558526585117)
          ·
            refine ⟨8155567034781209447469419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21748178759416558526585117 8155567034781209447469419)
            ·
              refine ⟨12233350552171814171204129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8155567034781209447469419 12233350552171814171204129)
              ·
                refine ⟨9175012914128860628403097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233350552171814171204129 9175012914128860628403097)
                ·
                  refine ⟨6881259685596645471302323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175012914128860628403097 6881259685596645471302323)
                  ·
                    refine ⟨10321889528394968206953485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881259685596645471302323 10321889528394968206953485)
                    ·
                      refine ⟨3870708573148113077607557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10321889528394968206953485 3870708573148113077607557)
                      ·
                        rfl

theorem cell23_7538178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7538178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538178 prefixEnd_7538178 := by exact prefixLift 7538178
  have htrace : WordTrace (prefixWord ++ tailWord_7538178) baseStart_7538178 baseEnd_7538178 := by
    simpa [prefixWord, tailWord_7538178, baseEnd_7538178] using wordTrace_append hprefix tailTrace_7538178
  have hstable : (prefixWord ++ tailWord_7538178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538178).length < 2 ^ (prefixWord ++ tailWord_7538178).sum := by decide
  have hdescent : baseEnd_7538178 < baseStart_7538178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538247 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_7538247 : Nat := 118140960795 + 7538247 * 2 ^ 59
def prefixEnd_7538247 : Nat := 4983230072969 + 3 ^ 40 * 7538247 * 2
def baseEnd_7538247 : Nat := 3870744003313273307644739

theorem tailTrace_7538247 : CollatzResearch.WordTrace tailWord_7538247 prefixEnd_7538247 3870744003313273307644739 := by
  unfold tailWord_7538247
  simp only [CollatzResearch.WordTrace]
  refine ⟨274942455521226023935164995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183294970347484015956776663 274942455521226023935164995)
  ·
    refine ⟨412413683281839035902747493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274942455521226023935164995 412413683281839035902747493)
    ·
      refine ⟨77327565615344819231765155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412413683281839035902747493 77327565615344819231765155)
      ·
        refine ⟨115991348423017228847647733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77327565615344819231765155 115991348423017228847647733)
        ·
          refine ⟨10874188914657865204466975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115991348423017228847647733 10874188914657865204466975)
          ·
            refine ⟨16311283371986797806700463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874188914657865204466975 16311283371986797806700463)
            ·
              refine ⟨24466925057980196710050695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16311283371986797806700463 24466925057980196710050695)
              ·
                refine ⟨36700387586970295065076043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24466925057980196710050695 36700387586970295065076043)
                ·
                  refine ⟨55050581380455442597614065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36700387586970295065076043 55050581380455442597614065)
                  ·
                    refine ⟨41287936035341581948210549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55050581380455442597614065 41287936035341581948210549)
                    ·
                      refine ⟨3870744003313273307644739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41287936035341581948210549 3870744003313273307644739)
                      ·
                        rfl

theorem cell23_7538247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_7538247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538247 prefixEnd_7538247 := by exact prefixLift 7538247
  have htrace : WordTrace (prefixWord ++ tailWord_7538247) baseStart_7538247 baseEnd_7538247 := by
    simpa [prefixWord, tailWord_7538247, baseEnd_7538247] using wordTrace_append hprefix tailTrace_7538247
  have hstable : (prefixWord ++ tailWord_7538247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538247).length < 2 ^ (prefixWord ++ tailWord_7538247).sum := by decide
  have hdescent : baseEnd_7538247 < baseStart_7538247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538257 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_7538257 : Nat := 118140960795 + 7538257 * 2 ^ 59
def prefixEnd_7538257 : Nat := 4983230072969 + 3 ^ 40 * 7538257 * 2
def baseEnd_7538257 : Nat := 3870749138119818268519693

theorem tailTrace_7538257 : CollatzResearch.WordTrace tailWord_7538257 prefixEnd_7538257 3870749138119818268519693 := by
  unfold tailWord_7538257
  simp only [CollatzResearch.WordTrace]
  refine ⟨274942820251189795643029025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183295213500793197095352683 274942820251189795643029025)
  ·
    refine ⟨206207115188392346732271769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274942820251189795643029025 206207115188392346732271769)
    ·
      refine ⟨154655336391294260049203827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206207115188392346732271769 154655336391294260049203827)
      ·
        refine ⟨231983004586941390073805741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154655336391294260049203827 231983004586941390073805741)
        ·
          refine ⟨86993626720103021277677153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231983004586941390073805741 86993626720103021277677153)
          ·
            refine ⟨65245220040077265958257865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86993626720103021277677153 65245220040077265958257865)
            ·
              refine ⟨48933915030057949468693399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65245220040077265958257865 48933915030057949468693399)
              ·
                refine ⟨73400872545086924203040099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48933915030057949468693399 73400872545086924203040099)
                ·
                  refine ⟨110101308817630386304560149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73400872545086924203040099 110101308817630386304560149)
                  ·
                    refine ⟨5160998850826424358026257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110101308817630386304560149 5160998850826424358026257)
                    ·
                      refine ⟨3870749138119818268519693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5160998850826424358026257 3870749138119818268519693)
                      ·
                        rfl

theorem cell23_7538257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_7538257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538257 prefixEnd_7538257 := by exact prefixLift 7538257
  have htrace : WordTrace (prefixWord ++ tailWord_7538257) baseStart_7538257 baseEnd_7538257 := by
    simpa [prefixWord, tailWord_7538257, baseEnd_7538257] using wordTrace_append hprefix tailTrace_7538257
  have hstable : (prefixWord ++ tailWord_7538257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538257).length < 2 ^ (prefixWord ++ tailWord_7538257).sum := by decide
  have hdescent : baseEnd_7538257 < baseStart_7538257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538284 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_7538284 : Nat := 118140960795 + 7538284 * 2 ^ 59
def prefixEnd_7538284 : Nat := 4983230072969 + 3 ^ 40 * 7538284 * 2
def baseEnd_7538284 : Nat := 1290254334032496554294023

theorem tailTrace_7538284 : CollatzResearch.WordTrace tailWord_7538284 prefixEnd_7538284 1290254334032496554294023 := by
  unfold tailWord_7538284
  simp only [CollatzResearch.WordTrace]
  refine ⟨137471902511045989627130953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183295870014727986169507937 137471902511045989627130953)
  ·
    refine ⟨103103926883284492220348215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137471902511045989627130953 103103926883284492220348215)
    ·
      refine ⟨154655890324926738330522323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103103926883284492220348215 154655890324926738330522323)
      ·
        refine ⟨231983835487390107495783485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154655890324926738330522323 231983835487390107495783485)
        ·
          refine ⟨86993938307771290310918807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231983835487390107495783485 86993938307771290310918807)
          ·
            refine ⟨130490907461656935466378211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86993938307771290310918807 130490907461656935466378211)
            ·
              refine ⟨195736361192485403199567317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130490907461656935466378211 195736361192485403199567317)
              ·
                refine ⟨4587570965448876637489859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195736361192485403199567317 4587570965448876637489859)
                ·
                  refine ⟨6881356448173314956234789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587570965448876637489859 6881356448173314956234789)
                  ·
                    refine ⟨1290254334032496554294023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881356448173314956234789 1290254334032496554294023)
                    ·
                      rfl

theorem cell23_7538284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_7538284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538284 prefixEnd_7538284 := by exact prefixLift 7538284
  have htrace : WordTrace (prefixWord ++ tailWord_7538284) baseStart_7538284 baseEnd_7538284 := by
    simpa [prefixWord, tailWord_7538284, baseEnd_7538284] using wordTrace_append hprefix tailTrace_7538284
  have hstable : (prefixWord ++ tailWord_7538284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538284).length < 2 ^ (prefixWord ++ tailWord_7538284).sum := by decide
  have hdescent : baseEnd_7538284 < baseStart_7538284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538297 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 6]
def baseStart_7538297 : Nat := 118140960795 + 7538297 * 2 ^ 59
def prefixEnd_7538297 : Nat := 4983230072969 + 3 ^ 40 * 7538297 * 2
def baseEnd_7538297 : Nat := 430085519705110901335501

theorem tailTrace_7538297 : CollatzResearch.WordTrace tailWord_7538297 prefixEnd_7538297 430085519705110901335501 := by
  unfold tailWord_7538297
  simp only [CollatzResearch.WordTrace]
  refine ⟨274944279171044882474485145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183296186114029921649656763 274944279171044882474485145)
  ·
    refine ⟨206208209378283661855863859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274944279171044882474485145 206208209378283661855863859)
    ·
      refine ⟨309312314067425492783795789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206208209378283661855863859 309312314067425492783795789)
      ·
        refine ⟨115992117775284559793923421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309312314067425492783795789 115992117775284559793923421)
        ·
          refine ⟨43497044165731709922721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115992117775284559793923421 43497044165731709922721283)
          ·
            refine ⟨65245566248597564884081925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43497044165731709922721283 65245566248597564884081925)
            ·
              refine ⟨12233543671612043415765361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65245566248597564884081925 12233543671612043415765361)
              ·
                refine ⟨9175157753709032561824021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233543671612043415765361 9175157753709032561824021)
                ·
                  refine ⟨430085519705110901335501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9175157753709032561824021 430085519705110901335501)
                  ·
                    rfl

theorem cell23_7538297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_7538297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538297 prefixEnd_7538297 := by exact prefixLift 7538297
  have htrace : WordTrace (prefixWord ++ tailWord_7538297) baseStart_7538297 baseEnd_7538297 := by
    simpa [prefixWord, tailWord_7538297, baseEnd_7538297] using wordTrace_append hprefix tailTrace_7538297
  have hstable : (prefixWord ++ tailWord_7538297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538297).length < 2 ^ (prefixWord ++ tailWord_7538297).sum := by decide
  have hdescent : baseEnd_7538297 < baseStart_7538297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538300 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7538300 : Nat := 118140960795 + 7538300 * 2 ^ 59
def prefixEnd_7538300 : Nat := 4983230072969 + 3 ^ 40 * 7538300 * 2
def baseEnd_7538300 : Nat := 3870771217787961600281995

theorem tailTrace_7538300 : CollatzResearch.WordTrace tailWord_7538300 prefixEnd_7538300 3870771217787961600281995 := by
  unfold tailWord_7538300
  simp only [CollatzResearch.WordTrace]
  refine ⟨137472194295017006993422177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183296259060022675991229569 137472194295017006993422177)
  ·
    refine ⟨103104145721262755245066633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137472194295017006993422177 103104145721262755245066633)
    ·
      refine ⟨77328109290947066433799975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103104145721262755245066633 77328109290947066433799975)
      ·
        refine ⟨115992163936420599650699963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77328109290947066433799975 115992163936420599650699963)
        ·
          refine ⟨173988245904630899476049945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115992163936420599650699963 173988245904630899476049945)
          ·
            refine ⟨130491184428473174607037459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173988245904630899476049945 130491184428473174607037459)
            ·
              refine ⟨195736776642709761910556189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130491184428473174607037459 195736776642709761910556189)
              ·
                refine ⟨73401291241016160716458571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195736776642709761910556189 73401291241016160716458571)
                ·
                  refine ⟨110101936861524241074687857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73401291241016160716458571 110101936861524241074687857)
                  ·
                    refine ⟨82576452646143180806015893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110101936861524241074687857 82576452646143180806015893)
                    ·
                      refine ⟨3870771217787961600281995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82576452646143180806015893 3870771217787961600281995)
                      ·
                        rfl

theorem cell23_7538300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7538300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538300 prefixEnd_7538300 := by exact prefixLift 7538300
  have htrace : WordTrace (prefixWord ++ tailWord_7538300) baseStart_7538300 baseEnd_7538300 := by
    simpa [prefixWord, tailWord_7538300, baseEnd_7538300] using wordTrace_append hprefix tailTrace_7538300
  have hstable : (prefixWord ++ tailWord_7538300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538300).length < 2 ^ (prefixWord ++ tailWord_7538300).sum := by decide
  have hdescent : baseEnd_7538300 < baseStart_7538300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538301 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_7538301 : Nat := 118140960795 + 7538301 * 2 ^ 59
def prefixEnd_7538301 : Nat := 4983230072969 + 3 ^ 40 * 7538301 * 2
def baseEnd_7538301 : Nat := 1290257243756205365456497

theorem tailTrace_7538301 : CollatzResearch.WordTrace tailWord_7538301 prefixEnd_7538301 1290257243756205365456497 := by
  unfold tailWord_7538301
  simp only [CollatzResearch.WordTrace]
  refine ⟨274944425063030391157630757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183296283375353594105087171 274944425063030391157630757)
  ·
    refine ⟨51552079699318198342055767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274944425063030391157630757 51552079699318198342055767)
    ·
      refine ⟨77328119548977297513083651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51552079699318198342055767 77328119548977297513083651)
      ·
        refine ⟨115992179323465946269625477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77328119548977297513083651 115992179323465946269625477)
        ·
          refine ⟨21748533623149864925554777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115992179323465946269625477 21748533623149864925554777)
          ·
            refine ⟨16311400217362398694166083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21748533623149864925554777 16311400217362398694166083)
            ·
              refine ⟨24467100326043598041249125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16311400217362398694166083 24467100326043598041249125)
              ·
                refine ⟨4587581311133174632734211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24467100326043598041249125 4587581311133174632734211)
                ·
                  refine ⟨6881371966699761949101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587581311133174632734211 6881371966699761949101317)
                  ·
                    refine ⟨1290257243756205365456497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881371966699761949101317 1290257243756205365456497)
                    ·
                      rfl

theorem cell23_7538301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_7538301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538301 prefixEnd_7538301 := by exact prefixLift 7538301
  have htrace : WordTrace (prefixWord ++ tailWord_7538301) baseStart_7538301 baseEnd_7538301 := by
    simpa [prefixWord, tailWord_7538301, baseEnd_7538301] using wordTrace_append hprefix tailTrace_7538301
  have hstable : (prefixWord ++ tailWord_7538301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538301).length < 2 ^ (prefixWord ++ tailWord_7538301).sum := by decide
  have hdescent : baseEnd_7538301 < baseStart_7538301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538327 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 3, 5]
def baseStart_7538327 : Nat := 118140960795 + 7538327 * 2 ^ 59
def prefixEnd_7538327 : Nat := 4983230072969 + 3 ^ 40 * 7538327 * 2
def baseEnd_7538327 : Nat := 1290261693921877664881457

theorem tailTrace_7538327 : CollatzResearch.WordTrace tailWord_7538327 prefixEnd_7538327 1290261693921877664881457 := by
  unfold tailWord_7538327
  simp only [CollatzResearch.WordTrace]
  refine ⟨274945373360936197598077235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183296915573957465065384823 274945373360936197598077235)
  ·
    refine ⟨412418060041404296397115853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274945373360936197598077235 412418060041404296397115853)
    ·
      refine ⟨154656772515526611148918445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412418060041404296397115853 154656772515526611148918445)
      ·
        refine ⟨57996289693322479180844417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154656772515526611148918445 57996289693322479180844417)
        ·
          refine ⟨43497217269991859385633313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57996289693322479180844417 43497217269991859385633313)
          ·
            refine ⟨32622912952493894539224985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43497217269991859385633313 32622912952493894539224985)
            ·
              refine ⟨24467184714370420904418739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32622912952493894539224985 24467184714370420904418739)
              ·
                refine ⟨36700777071555631356628109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24467184714370420904418739 36700777071555631356628109)
                ·
                  refine ⟨13762791401833361758735541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36700777071555631356628109 13762791401833361758735541)
                  ·
                    refine ⟨1290261693921877664881457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13762791401833361758735541 1290261693921877664881457)
                    ·
                      rfl

theorem cell23_7538327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_7538327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538327 prefixEnd_7538327 := by exact prefixLift 7538327
  have htrace : WordTrace (prefixWord ++ tailWord_7538327) baseStart_7538327 baseEnd_7538327 := by
    simpa [prefixWord, tailWord_7538327, baseEnd_7538327] using wordTrace_append hprefix tailTrace_7538327
  have hstable : (prefixWord ++ tailWord_7538327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538327).length < 2 ^ (prefixWord ++ tailWord_7538327).sum := by decide
  have hdescent : baseEnd_7538327 < baseStart_7538327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538341 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 1, 1, 3]
def baseStart_7538341 : Nat := 118140960795 + 7538341 * 2 ^ 59
def prefixEnd_7538341 : Nat := 4983230072969 + 3 ^ 40 * 7538341 * 2
def baseEnd_7538341 : Nat := 3870792270494795939869307

theorem tailTrace_7538341 : CollatzResearch.WordTrace tailWord_7538341 prefixEnd_7538341 3870792270494795939869307 := by
  unfold tailWord_7538341
  simp only [CollatzResearch.WordTrace]
  refine ⟨274945883982885477989086877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183297255988590318659391251 274945883982885477989086877)
  ·
    refine ⟨103104706493582054245907579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274945883982885477989086877 103104706493582054245907579)
    ·
      refine ⟨154657059740373081368861369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103104706493582054245907579 154657059740373081368861369)
      ·
        refine ⟨115992794805279811026646027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154657059740373081368861369 115992794805279811026646027)
        ·
          refine ⟨173989192207919716539969041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115992794805279811026646027 173989192207919716539969041)
          ·
            refine ⟨130491894155939787404976781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173989192207919716539969041 130491894155939787404976781)
            ·
              refine ⟨48934460308477420276866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130491894155939787404976781 48934460308477420276866293)
              ·
                refine ⟨4587605653919758150956215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48934460308477420276866293 4587605653919758150956215)
                ·
                  refine ⟨6881408480879637226434323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587605653919758150956215 6881408480879637226434323)
                  ·
                    refine ⟨10322112721319455839651485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881408480879637226434323 10322112721319455839651485)
                    ·
                      refine ⟨3870792270494795939869307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322112721319455839651485 3870792270494795939869307)
                      ·
                        rfl

theorem cell23_7538341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_7538341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538341 prefixEnd_7538341 := by exact prefixLift 7538341
  have htrace : WordTrace (prefixWord ++ tailWord_7538341) baseStart_7538341 baseEnd_7538341 := by
    simpa [prefixWord, tailWord_7538341, baseEnd_7538341] using wordTrace_append hprefix tailTrace_7538341
  have hstable : (prefixWord ++ tailWord_7538341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538341).length < 2 ^ (prefixWord ++ tailWord_7538341).sum := by decide
  have hdescent : baseEnd_7538341 < baseStart_7538341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538358 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_7538358 : Nat := 118140960795 + 7538358 * 2 ^ 59
def prefixEnd_7538358 : Nat := 4983230072969 + 3 ^ 40 * 7538358 * 2
def baseEnd_7538358 : Nat := 3870800999665922373356729

theorem tailTrace_7538358 : CollatzResearch.WordTrace tailWord_7538358 prefixEnd_7538358 3870800999665922373356729 := by
  unfold tailWord_7538358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184156501488993118278483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183297669349215926594970485 17184156501488993118278483)
  ·
    refine ⟨25776234752233489677417725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17184156501488993118278483 25776234752233489677417725)
    ·
      refine ⟨9666088032087558629031647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25776234752233489677417725 9666088032087558629031647)
      ·
        refine ⟨14499132048131337943547471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9666088032087558629031647 14499132048131337943547471)
        ·
          refine ⟨21748698072197006915321207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14499132048131337943547471 21748698072197006915321207)
          ·
            refine ⟨32623047108295510372981811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21748698072197006915321207 32623047108295510372981811)
            ·
              refine ⟨48934570662443265559472717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32623047108295510372981811 48934570662443265559472717)
              ·
                refine ⟨18350463998416224584802269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48934570662443265559472717 18350463998416224584802269)
                ·
                  refine ⟨6881423999406084219300851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18350463998416224584802269 6881423999406084219300851)
                  ·
                    refine ⟨10322135999109126328951277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881423999406084219300851 10322135999109126328951277)
                    ·
                      refine ⟨3870800999665922373356729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322135999109126328951277 3870800999665922373356729)
                      ·
                        rfl

theorem cell23_7538358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_7538358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538358 prefixEnd_7538358 := by exact prefixLift 7538358
  have htrace : WordTrace (prefixWord ++ tailWord_7538358) baseStart_7538358 baseEnd_7538358 := by
    simpa [prefixWord, tailWord_7538358, baseEnd_7538358] using wordTrace_append hprefix tailTrace_7538358
  have hstable : (prefixWord ++ tailWord_7538358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538358).length < 2 ^ (prefixWord ++ tailWord_7538358).sum := by decide
  have hdescent : baseEnd_7538358 < baseStart_7538358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538367 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_7538367 : Nat := 118140960795 + 7538367 * 2 ^ 59
def prefixEnd_7538367 : Nat := 4983230072969 + 3 ^ 40 * 7538367 * 2
def baseEnd_7538367 : Nat := 3870805620991812838144187

theorem tailTrace_7538367 : CollatzResearch.WordTrace tailWord_7538367 prefixEnd_7538367 3870805620991812838144187 := by
  unfold tailWord_7538367
  simp only [CollatzResearch.WordTrace]
  refine ⟨274946832280791284429533355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183297888187194189619688903 274946832280791284429533355)
  ·
    refine ⟨412420248421186926644300033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274946832280791284429533355 412420248421186926644300033)
    ·
      refine ⟨309315186315890194983225025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412420248421186926644300033 309315186315890194983225025)
      ·
        refine ⟨231986389736917646237418769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309315186315890194983225025 231986389736917646237418769)
        ·
          refine ⟨173989792302688234678064077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231986389736917646237418769 173989792302688234678064077)
          ·
            refine ⟨65246172113508088004274029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173989792302688234678064077 65246172113508088004274029)
            ·
              refine ⟨24467314542565533001602761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65246172113508088004274029 24467314542565533001602761)
              ·
                refine ⟨18350485906924149751202071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24467314542565533001602761 18350485906924149751202071)
                ·
                  refine ⟨27525728860386224626803107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18350485906924149751202071 27525728860386224626803107)
                  ·
                    refine ⟨41288593290579336940204661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27525728860386224626803107 41288593290579336940204661)
                    ·
                      refine ⟨3870805620991812838144187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41288593290579336940204661 3870805620991812838144187)
                      ·
                        rfl

theorem cell23_7538367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_7538367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538367 prefixEnd_7538367 := by exact prefixLift 7538367
  have htrace : WordTrace (prefixWord ++ tailWord_7538367) baseStart_7538367 baseEnd_7538367 := by
    simpa [prefixWord, tailWord_7538367, baseEnd_7538367] using wordTrace_append hprefix tailTrace_7538367
  have hstable : (prefixWord ++ tailWord_7538367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538367).length < 2 ^ (prefixWord ++ tailWord_7538367).sum := by decide
  have hdescent : baseEnd_7538367 < baseStart_7538367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538415 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 1, 2, 2]
def baseStart_7538415 : Nat := 118140960795 + 7538415 * 2 ^ 59
def prefixEnd_7538415 : Nat := 4983230072969 + 3 ^ 40 * 7538415 * 2
def baseEnd_7538415 : Nat := 3870830268063228650343967

theorem tailTrace_7538415 : CollatzResearch.WordTrace tailWord_7538415 prefixEnd_7538415 3870830268063228650343967 := by
  unfold tailWord_7538415
  simp only [CollatzResearch.WordTrace]
  refine ⟨274948582984617388627280699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183299055323078259084853799 274948582984617388627280699)
  ·
    refine ⟨412422874476926082940921049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274948582984617388627280699 412422874476926082940921049)
    ·
      refine ⟨309317155857694562205690787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412422874476926082940921049 309317155857694562205690787)
      ·
        refine ⟨463975733786541843308536181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309317155857694562205690787 463975733786541843308536181)
        ·
          refine ⟨43497725042488297810175267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 463975733786541843308536181 43497725042488297810175267)
          ·
            refine ⟨65246587563732446715262901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43497725042488297810175267 65246587563732446715262901)
            ·
              refine ⟨6116867584099916879555897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65246587563732446715262901 6116867584099916879555897)
              ·
                refine ⟨4587650688074937659666923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116867584099916879555897 4587650688074937659666923)
                ·
                  refine ⟨6881476032112406489500385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587650688074937659666923 6881476032112406489500385)
                  ·
                    refine ⟨5161107024084304867125289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6881476032112406489500385 5161107024084304867125289)
                    ·
                      refine ⟨3870830268063228650343967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161107024084304867125289 3870830268063228650343967)
                      ·
                        rfl

theorem cell23_7538415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 2, 2].length) (baseStart_7538415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538415 prefixEnd_7538415 := by exact prefixLift 7538415
  have htrace : WordTrace (prefixWord ++ tailWord_7538415) baseStart_7538415 baseEnd_7538415 := by
    simpa [prefixWord, tailWord_7538415, baseEnd_7538415] using wordTrace_append hprefix tailTrace_7538415
  have hstable : (prefixWord ++ tailWord_7538415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538415).length < 2 ^ (prefixWord ++ tailWord_7538415).sum := by decide
  have hdescent : baseEnd_7538415 < baseStart_7538415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538452 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7538452 : Nat := 118140960795 + 7538452 * 2 ^ 59
def prefixEnd_7538452 : Nat := 4983230072969 + 3 ^ 40 * 7538452 * 2
def baseEnd_7538452 : Nat := 3870849266847445005581297

theorem tailTrace_7538452 : CollatzResearch.WordTrace tailWord_7538452 prefixEnd_7538452 3870849266847445005581297 := by
  unfold tailWord_7538452
  simp only [CollatzResearch.WordTrace]
  refine ⟨137474966242741671973188805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183299954990322229297585073 137474966242741671973188805)
  ·
    refine ⟨25776556170514063494972901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137474966242741671973188805 25776556170514063494972901)
    ·
      refine ⟨4833104281971386905307419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25776556170514063494972901 4833104281971386905307419)
      ·
        refine ⟨7249656422957080357961129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833104281971386905307419 7249656422957080357961129)
        ·
          refine ⟨5437242317217810268470847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7249656422957080357961129 5437242317217810268470847)
          ·
            refine ⟨8155863475826715402706271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437242317217810268470847 8155863475826715402706271)
            ·
              refine ⟨12233795213740073104059407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8155863475826715402706271 12233795213740073104059407)
              ·
                refine ⟨18350692820610109656089111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12233795213740073104059407 18350692820610109656089111)
                ·
                  refine ⟨27526039230915164484133667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18350692820610109656089111 27526039230915164484133667)
                  ·
                    refine ⟨41289058846372746726200501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27526039230915164484133667 41289058846372746726200501)
                    ·
                      refine ⟨3870849266847445005581297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41289058846372746726200501 3870849266847445005581297)
                      ·
                        rfl

theorem cell23_7538452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7538452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538452 prefixEnd_7538452 := by exact prefixLift 7538452
  have htrace : WordTrace (prefixWord ++ tailWord_7538452) baseStart_7538452 baseEnd_7538452 := by
    simpa [prefixWord, tailWord_7538452, baseEnd_7538452] using wordTrace_append hprefix tailTrace_7538452
  have hstable : (prefixWord ++ tailWord_7538452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538452).length < 2 ^ (prefixWord ++ tailWord_7538452).sum := by decide
  have hdescent : baseEnd_7538452 < baseStart_7538452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538488 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_7538488 : Nat := 118140960795 + 7538488 * 2 ^ 59
def prefixEnd_7538488 : Nat := 4983230072969 + 3 ^ 40 * 7538488 * 2
def baseEnd_7538488 : Nat := 3870867752151006864731131

theorem tailTrace_7538488 : CollatzResearch.WordTrace tailWord_7538488 prefixEnd_7538488 3870867752151006864731131 := by
  unfold tailWord_7538488
  simp only [CollatzResearch.WordTrace]
  refine ⟨137475622756676461047344059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183300830342235281396458745 137475622756676461047344059)
  ·
    refine ⟨206213434135014691571016089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137475622756676461047344059 206213434135014691571016089)
    ·
      refine ⟨154660075601261018678262067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206213434135014691571016089 154660075601261018678262067)
      ·
        refine ⟨231990113401891528017393101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154660075601261018678262067 231990113401891528017393101)
        ·
          refine ⟨86996292525709323006522413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231990113401891528017393101 86996292525709323006522413)
          ·
            refine ⟨32623609697140996127445905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86996292525709323006522413 32623609697140996127445905)
            ·
              refine ⟨24467707272855747095584429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32623609697140996127445905 24467707272855747095584429)
              ·
                refine ⟨9175390227320905160844161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24467707272855747095584429 9175390227320905160844161)
                ·
                  refine ⟨6881542670490678870633121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175390227320905160844161 6881542670490678870633121)
                  ·
                    refine ⟨5161157002868009152974841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6881542670490678870633121 5161157002868009152974841)
                    ·
                      refine ⟨3870867752151006864731131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161157002868009152974841 3870867752151006864731131)
                      ·
                        rfl

theorem cell23_7538488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_7538488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538488 prefixEnd_7538488 := by exact prefixLift 7538488
  have htrace : WordTrace (prefixWord ++ tailWord_7538488) baseStart_7538488 baseEnd_7538488 := by
    simpa [prefixWord, tailWord_7538488, baseEnd_7538488] using wordTrace_append hprefix tailTrace_7538488
  have hstable : (prefixWord ++ tailWord_7538488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538488).length < 2 ^ (prefixWord ++ tailWord_7538488).sum := by decide
  have hdescent : baseEnd_7538488 < baseStart_7538488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538494 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_7538494 : Nat := 118140960795 + 7538494 * 2 ^ 59
def prefixEnd_7538494 : Nat := 4983230072969 + 3 ^ 40 * 7538494 * 2
def baseEnd_7538494 : Nat := 430096759226103760139567

theorem tailTrace_7538494 : CollatzResearch.WordTrace tailWord_7538494 prefixEnd_7538494 430096759226103760139567 := by
  unfold tailWord_7538494
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368933043916398139925817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183300976234220790079604357 34368933043916398139925817)
  ·
    refine ⟨25776699782937298604944363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34368933043916398139925817 25776699782937298604944363)
    ·
      refine ⟨38665049674405947907416545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25776699782937298604944363 38665049674405947907416545)
      ·
        refine ⟨28998787255804460930562409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38665049674405947907416545 28998787255804460930562409)
        ·
          refine ⟨21749090441853345697921807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28998787255804460930562409 21749090441853345697921807)
          ·
            refine ⟨32623635662780018546882711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21749090441853345697921807 32623635662780018546882711)
            ·
              refine ⟨48935453494170027820324067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32623635662780018546882711 48935453494170027820324067)
              ·
                refine ⟨73403180241255041730486101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48935453494170027820324067 73403180241255041730486101)
                ·
                  refine ⟨430096759226103760139567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73403180241255041730486101 430096759226103760139567)
                  ·
                    rfl

theorem cell23_7538494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_7538494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538494 prefixEnd_7538494 := by exact prefixLift 7538494
  have htrace : WordTrace (prefixWord ++ tailWord_7538494) baseStart_7538494 baseEnd_7538494 := by
    simpa [prefixWord, tailWord_7538494, baseEnd_7538494] using wordTrace_append hprefix tailTrace_7538494
  have hstable : (prefixWord ++ tailWord_7538494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538494).length < 2 ^ (prefixWord ++ tailWord_7538494).sum := by decide
  have hdescent : baseEnd_7538494 < baseStart_7538494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538578 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7538578 : Nat := 118140960795 + 7538578 * 2 ^ 59
def prefixEnd_7538578 : Nat := 4983230072969 + 3 ^ 40 * 7538578 * 2
def baseEnd_7538578 : Nat := 3870913965409911512605717

theorem tailTrace_7538578 : CollatzResearch.WordTrace tailWord_7538578 prefixEnd_7538578 3870913965409911512605717 := by
  unfold tailWord_7538578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68738632020756716866366097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183303018722017911643642925 68738632020756716866366097)
  ·
    refine ⟨51553974015567537649774573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68738632020756716866366097 51553974015567537649774573)
    ·
      refine ⟨19332740255837826618665465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51553974015567537649774573 19332740255837826618665465)
      ·
        refine ⟨14499555191878369963999099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19332740255837826618665465 14499555191878369963999099)
        ·
          refine ⟨21749332787817554945998649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14499555191878369963999099 21749332787817554945998649)
          ·
            refine ⟨16311999590863166209498987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21749332787817554945998649 16311999590863166209498987)
            ·
              refine ⟨24467999386294749314248481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16311999590863166209498987 24467999386294749314248481)
              ·
                refine ⟨18350999539721061985686361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24467999386294749314248481 18350999539721061985686361)
                ·
                  refine ⟨13763249654790796489264771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18350999539721061985686361 13763249654790796489264771)
                  ·
                    refine ⟨20644874482186194733897157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13763249654790796489264771 20644874482186194733897157)
                    ·
                      refine ⟨3870913965409911512605717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20644874482186194733897157 3870913965409911512605717)
                      ·
                        rfl

theorem cell23_7538578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7538578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538578 prefixEnd_7538578 := by exact prefixLift 7538578
  have htrace : WordTrace (prefixWord ++ tailWord_7538578) baseStart_7538578 baseEnd_7538578 := by
    simpa [prefixWord, tailWord_7538578, baseEnd_7538578] using wordTrace_append hprefix tailTrace_7538578
  have hstable : (prefixWord ++ tailWord_7538578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538578).length < 2 ^ (prefixWord ++ tailWord_7538578).sum := by decide
  have hdescent : baseEnd_7538578 < baseStart_7538578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538581 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_7538581 : Nat := 118140960795 + 7538581 * 2 ^ 59
def prefixEnd_7538581 : Nat := 4983230072969 + 3 ^ 40 * 7538581 * 2
def baseEnd_7538581 : Nat := 3870915505851875000868203

theorem tailTrace_7538581 : CollatzResearch.WordTrace tailWord_7538581 prefixEnd_7538581 3870915505851875000868203 := by
  unfold tailWord_7538581
  simp only [CollatzResearch.WordTrace]
  refine ⟨274954637502015998977823597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183303091668010665985215731 274954637502015998977823597)
  ·
    refine ⟨103107989063255999616683849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274954637502015998977823597 103107989063255999616683849)
    ·
      refine ⟨77330991797441999712512887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103107989063255999616683849 77330991797441999712512887)
      ·
        refine ⟨115996487696162999568769331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77330991797441999712512887 115996487696162999568769331)
        ·
          refine ⟨173994731544244499353153997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115996487696162999568769331 173994731544244499353153997)
          ·
            refine ⟨65248024329091687257432749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173994731544244499353153997 65248024329091687257432749)
            ·
              refine ⟨24468009123409382721537281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65248024329091687257432749 24468009123409382721537281)
              ·
                refine ⟨18351006842557037041152961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24468009123409382721537281 18351006842557037041152961)
                ·
                  refine ⟨13763255131917777780864721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18351006842557037041152961 13763255131917777780864721)
                  ·
                    refine ⟨10322441348938333335648541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13763255131917777780864721 10322441348938333335648541)
                    ·
                      refine ⟨3870915505851875000868203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322441348938333335648541 3870915505851875000868203)
                      ·
                        rfl

theorem cell23_7538581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_7538581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538581 prefixEnd_7538581 := by exact prefixLift 7538581
  have htrace : WordTrace (prefixWord ++ tailWord_7538581) baseStart_7538581 baseEnd_7538581 := by
    simpa [prefixWord, tailWord_7538581, baseEnd_7538581] using wordTrace_append hprefix tailTrace_7538581
  have hstable : (prefixWord ++ tailWord_7538581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538581).length < 2 ^ (prefixWord ++ tailWord_7538581).sum := by decide
  have hdescent : baseEnd_7538581 < baseStart_7538581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538588 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 3, 4]
def baseStart_7538588 : Nat := 118140960795 + 7538588 * 2 ^ 59
def prefixEnd_7538588 : Nat := 4983230072969 + 3 ^ 40 * 7538588 * 2
def baseEnd_7538588 : Nat := 1290306366738818824493557

theorem tailTrace_7538588 : CollatzResearch.WordTrace tailWord_7538588 prefixEnd_7538588 1290306366738818824493557 := by
  unfold tailWord_7538588
  simp only [CollatzResearch.WordTrace]
  refine ⟨137477446406495319586664209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183303261875327092782218945 137477446406495319586664209)
  ·
    refine ⟨103108084804871489689998157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137477446406495319586664209 103108084804871489689998157)
    ·
      refine ⟨38665531801826808633749309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103108084804871489689998157 38665531801826808633749309)
      ·
        refine ⟨14499574425685053237655991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38665531801826808633749309 14499574425685053237655991)
        ·
          refine ⟨21749361638527579856483987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14499574425685053237655991 21749361638527579856483987)
          ·
            refine ⟨32624042457791369784725981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21749361638527579856483987 32624042457791369784725981)
            ·
              refine ⟨12234015921671763669272243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32624042457791369784725981 12234015921671763669272243)
              ·
                refine ⟨18351023882507645503908365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234015921671763669272243 18351023882507645503908365)
                ·
                  refine ⟨6881633955940367063965637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18351023882507645503908365 6881633955940367063965637)
                  ·
                    refine ⟨1290306366738818824493557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881633955940367063965637 1290306366738818824493557)
                    ·
                      rfl

theorem cell23_7538588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_7538588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538588 prefixEnd_7538588 := by exact prefixLift 7538588
  have htrace : WordTrace (prefixWord ++ tailWord_7538588) baseStart_7538588 baseEnd_7538588 := by
    simpa [prefixWord, tailWord_7538588, baseEnd_7538588] using wordTrace_append hprefix tailTrace_7538588
  have hstable : (prefixWord ++ tailWord_7538588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538588).length < 2 ^ (prefixWord ++ tailWord_7538588).sum := by decide
  have hdescent : baseEnd_7538588 < baseStart_7538588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538611 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 3]
def baseStart_7538611 : Nat := 118140960795 + 7538611 * 2 ^ 59
def prefixEnd_7538611 : Nat := 4983230072969 + 3 ^ 40 * 7538611 * 2
def baseEnd_7538611 : Nat := 3870930910271509883493065

theorem tailTrace_7538611 : CollatzResearch.WordTrace tailWord_7538611 prefixEnd_7538611 3870930910271509883493065 := by
  unfold tailWord_7538611
  simp only [CollatzResearch.WordTrace]
  refine ⟨274955731691907314101415687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183303821127938209400943791 274955731691907314101415687)
  ·
    refine ⟨412433597537860971152123531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274955731691907314101415687 412433597537860971152123531)
    ·
      refine ⟨618650396306791456728185297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412433597537860971152123531 618650396306791456728185297)
      ·
        refine ⟨463987797230093592546138973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618650396306791456728185297 463987797230093592546138973)
        ·
          refine ⟨173995423961285097204802115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463987797230093592546138973 173995423961285097204802115)
          ·
            refine ⟨260993135941927645807203173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173995423961285097204802115 260993135941927645807203173)
            ·
              refine ⟨48936212989111433588850595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260993135941927645807203173 48936212989111433588850595)
              ·
                refine ⟨73404319483667150383275893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48936212989111433588850595 73404319483667150383275893)
                ·
                  refine ⟨6881654951593795348432115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73404319483667150383275893 6881654951593795348432115)
                  ·
                    refine ⟨10322482427390693022648173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6881654951593795348432115 10322482427390693022648173)
                    ·
                      refine ⟨3870930910271509883493065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322482427390693022648173 3870930910271509883493065)
                      ·
                        rfl

theorem cell23_7538611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_7538611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538611 prefixEnd_7538611 := by exact prefixLift 7538611
  have htrace : WordTrace (prefixWord ++ tailWord_7538611) baseStart_7538611 baseEnd_7538611 := by
    simpa [prefixWord, tailWord_7538611, baseEnd_7538611] using wordTrace_append hprefix tailTrace_7538611
  have hstable : (prefixWord ++ tailWord_7538611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538611).length < 2 ^ (prefixWord ++ tailWord_7538611).sum := by decide
  have hdescent : baseEnd_7538611 < baseStart_7538611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538638 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_7538638 : Nat := 118140960795 + 7538638 * 2 ^ 59
def prefixEnd_7538638 : Nat := 4983230072969 + 3 ^ 40 * 7538638 * 2
def baseEnd_7538638 : Nat := 3870944774249181277855441

theorem tailTrace_7538638 : CollatzResearch.WordTrace tailWord_7538638 prefixEnd_7538638 3870944774249181277855441 := by
  unfold tailWord_7538638
  simp only [CollatzResearch.WordTrace]
  refine ⟨34369589557851187214081071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183304477641872998475099045 34369589557851187214081071)
  ·
    refine ⟨51554384336776780821121607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34369589557851187214081071 51554384336776780821121607)
    ·
      refine ⟨77331576505165171231682411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51554384336776780821121607 77331576505165171231682411)
      ·
        refine ⟨115997364757747756847523617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77331576505165171231682411 115997364757747756847523617)
        ·
          refine ⟨86998023568310817635642713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115997364757747756847523617 86998023568310817635642713)
          ·
            refine ⟨65248517676233113226732035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86998023568310817635642713 65248517676233113226732035)
            ·
              refine ⟨97872776514349669840098053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65248517676233113226732035 97872776514349669840098053)
              ·
                refine ⟨18351145596440563095018385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97872776514349669840098053 18351145596440563095018385)
                ·
                  refine ⟨13763359197330422321263789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18351145596440563095018385 13763359197330422321263789)
                  ·
                    refine ⟨5161259698998908370473921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13763359197330422321263789 5161259698998908370473921)
                    ·
                      refine ⟨3870944774249181277855441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161259698998908370473921 3870944774249181277855441)
                      ·
                        rfl

theorem cell23_7538638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_7538638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538638 prefixEnd_7538638 := by exact prefixLift 7538638
  have htrace : WordTrace (prefixWord ++ tailWord_7538638) baseStart_7538638 baseEnd_7538638 := by
    simpa [prefixWord, tailWord_7538638, baseEnd_7538638] using wordTrace_append hprefix tailTrace_7538638
  have hstable : (prefixWord ++ tailWord_7538638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538638).length < 2 ^ (prefixWord ++ tailWord_7538638).sum := by decide
  have hdescent : baseEnd_7538638 < baseStart_7538638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538671 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_7538671 : Nat := 118140960795 + 7538671 * 2 ^ 59
def prefixEnd_7538671 : Nat := 4983230072969 + 3 ^ 40 * 7538671 * 2
def baseEnd_7538671 : Nat := 3870961719110779648742789

theorem tailTrace_7538671 : CollatzResearch.WordTrace tailWord_7538671 prefixEnd_7538671 3870961719110779648742789 := by
  unfold tailWord_7538671
  simp only [CollatzResearch.WordTrace]
  refine ⟨274957920071689944348599867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183305280047793296232399911 274957920071689944348599867)
  ·
    refine ⟨412436880107534916522899801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274957920071689944348599867 412436880107534916522899801)
    ·
      refine ⟨309327660080651187392174851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412436880107534916522899801 309327660080651187392174851)
      ·
        refine ⟨463991490120976781088262277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309327660080651187392174851 463991490120976781088262277)
        ·
          refine ⟨86998404397683146454049177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463991490120976781088262277 86998404397683146454049177)
          ·
            refine ⟨65248803298262359840536883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86998404397683146454049177 65248803298262359840536883)
            ·
              refine ⟨97873204947393539760805325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65248803298262359840536883 97873204947393539760805325)
              ·
                refine ⟨36702451855272577410301997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97873204947393539760805325 36702451855272577410301997)
                ·
                  refine ⟨13763419445727216528863249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36702451855272577410301997 13763419445727216528863249)
                  ·
                    refine ⟨10322564584295412396647437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13763419445727216528863249 10322564584295412396647437)
                    ·
                      refine ⟨3870961719110779648742789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322564584295412396647437 3870961719110779648742789)
                      ·
                        rfl

theorem cell23_7538671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_7538671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538671 prefixEnd_7538671 := by exact prefixLift 7538671
  have htrace : WordTrace (prefixWord ++ tailWord_7538671) baseStart_7538671 baseEnd_7538671 := by
    simpa [prefixWord, tailWord_7538671, baseEnd_7538671] using wordTrace_append hprefix tailTrace_7538671
  have hstable : (prefixWord ++ tailWord_7538671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538671).length < 2 ^ (prefixWord ++ tailWord_7538671).sum := by decide
  have hdescent : baseEnd_7538671 < baseStart_7538671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538681 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_7538681 : Nat := 118140960795 + 7538681 * 2 ^ 59
def prefixEnd_7538681 : Nat := 4983230072969 + 3 ^ 40 * 7538681 * 2
def baseEnd_7538681 : Nat := 3870966853917324609617743

theorem tailTrace_7538681 : CollatzResearch.WordTrace tailWord_7538681 prefixEnd_7538681 3870966853917324609617743 := by
  unfold tailWord_7538681
  simp only [CollatzResearch.WordTrace]
  refine ⟨274958284801653716056463897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183305523201102477370975931 274958284801653716056463897)
  ·
    refine ⟨206218713601240287042347923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274958284801653716056463897 206218713601240287042347923)
    ·
      refine ⟨309328070401860430563521885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206218713601240287042347923 309328070401860430563521885)
      ·
        refine ⟨115998026400697661461320707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309328070401860430563521885 115998026400697661461320707)
        ·
          refine ⟨173997039601046492191981061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115998026400697661461320707 173997039601046492191981061)
          ·
            refine ⟨32624444925196217285996449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173997039601046492191981061 32624444925196217285996449)
            ·
              refine ⟨24468333693897162964497337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32624444925196217285996449 24468333693897162964497337)
              ·
                refine ⟨18351250270422872223373003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24468333693897162964497337 18351250270422872223373003)
                ·
                  refine ⟨27526875405634308335059505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18351250270422872223373003 27526875405634308335059505)
                  ·
                    refine ⟨20645156554225731251294629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27526875405634308335059505 20645156554225731251294629)
                    ·
                      refine ⟨3870966853917324609617743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20645156554225731251294629 3870966853917324609617743)
                      ·
                        rfl

theorem cell23_7538681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_7538681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538681 prefixEnd_7538681 := by exact prefixLift 7538681
  have htrace : WordTrace (prefixWord ++ tailWord_7538681) baseStart_7538681 baseEnd_7538681 := by
    simpa [prefixWord, tailWord_7538681, baseEnd_7538681] using wordTrace_append hprefix tailTrace_7538681
  have hstable : (prefixWord ++ tailWord_7538681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538681).length < 2 ^ (prefixWord ++ tailWord_7538681).sum := by decide
  have hdescent : baseEnd_7538681 < baseStart_7538681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538695 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 2, 4]
def baseStart_7538695 : Nat := 118140960795 + 7538695 * 2 ^ 59
def prefixEnd_7538695 : Nat := 4983230072969 + 3 ^ 40 * 7538695 * 2
def baseEnd_7538695 : Nat := 1290324680882162518280893

theorem tailTrace_7538695 : CollatzResearch.WordTrace tailWord_7538695 prefixEnd_7538695 1290324680882162518280893 := by
  unfold tailWord_7538695
  simp only [CollatzResearch.WordTrace]
  refine ⟨274958795423602996447473539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183305863615735330964982359 274958795423602996447473539)
  ·
    refine ⟨412438193135404494671210309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274958795423602996447473539 412438193135404494671210309)
    ·
      refine ⟨77332161212888342750851933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412438193135404494671210309 77332161212888342750851933)
      ·
        refine ⟨28999560454833128531569475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77332161212888342750851933 28999560454833128531569475)
        ·
          refine ⟨43499340682249692797354213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28999560454833128531569475 43499340682249692797354213)
          ·
            refine ⟨8156126377921817399503915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43499340682249692797354213 8156126377921817399503915)
            ·
              refine ⟨12234189566882726099255873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156126377921817399503915 12234189566882726099255873)
              ·
                refine ⟨9175642175162044574441905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12234189566882726099255873 9175642175162044574441905)
                ·
                  refine ⟨6881731631371533430831429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175642175162044574441905 6881731631371533430831429)
                  ·
                    refine ⟨1290324680882162518280893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881731631371533430831429 1290324680882162518280893)
                    ·
                      rfl

theorem cell23_7538695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_7538695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538695 prefixEnd_7538695 := by exact prefixLift 7538695
  have htrace : WordTrace (prefixWord ++ tailWord_7538695) baseStart_7538695 baseEnd_7538695 := by
    simpa [prefixWord, tailWord_7538695, baseEnd_7538695] using wordTrace_append hprefix tailTrace_7538695
  have hstable : (prefixWord ++ tailWord_7538695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538695).length < 2 ^ (prefixWord ++ tailWord_7538695).sum := by decide
  have hdescent : baseEnd_7538695 < baseStart_7538695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538702 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7538702 : Nat := 118140960795 + 7538702 * 2 ^ 59
def prefixEnd_7538702 : Nat := 4983230072969 + 3 ^ 40 * 7538702 * 2
def baseEnd_7538702 : Nat := 3870977637011069027455147

theorem tailTrace_7538702 : CollatzResearch.WordTrace tailWord_7538702 prefixEnd_7538702 3870977637011069027455147 := by
  unfold tailWord_7538702
  simp only [CollatzResearch.WordTrace]
  refine ⟨34369881341822204580372295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183306033823051757761985573 34369881341822204580372295)
  ·
    refine ⟨51554822012733306870558443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34369881341822204580372295 51554822012733306870558443)
    ·
      refine ⟨77332233019099960305837665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51554822012733306870558443 77332233019099960305837665)
      ·
        refine ⟨57999174764324970229378249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77332233019099960305837665 57999174764324970229378249)
        ·
          refine ⟨43499381073243727672033687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57999174764324970229378249 43499381073243727672033687)
          ·
            refine ⟨65249071609865591508050531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43499381073243727672033687 65249071609865591508050531)
            ·
              refine ⟨97873607414798387262075797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65249071609865591508050531 97873607414798387262075797)
              ·
                refine ⟨4587825347568674402909803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97873607414798387262075797 4587825347568674402909803)
                ·
                  refine ⟨6881738021353011604364705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587825347568674402909803 6881738021353011604364705)
                  ·
                    refine ⟨5161303516014758703273529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6881738021353011604364705 5161303516014758703273529)
                    ·
                      refine ⟨3870977637011069027455147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161303516014758703273529 3870977637011069027455147)
                      ·
                        rfl

theorem cell23_7538702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7538702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538702 prefixEnd_7538702 := by exact prefixLift 7538702
  have htrace : WordTrace (prefixWord ++ tailWord_7538702) baseStart_7538702 baseEnd_7538702 := by
    simpa [prefixWord, tailWord_7538702, baseEnd_7538702] using wordTrace_append hprefix tailTrace_7538702
  have hstable : (prefixWord ++ tailWord_7538702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538702).length < 2 ^ (prefixWord ++ tailWord_7538702).sum := by decide
  have hdescent : baseEnd_7538702 < baseStart_7538702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538761 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_7538761 : Nat := 118140960795 + 7538761 * 2 ^ 59
def prefixEnd_7538761 : Nat := 4983230072969 + 3 ^ 40 * 7538761 * 2
def baseEnd_7538761 : Nat := 3871007932369684296617375

theorem tailTrace_7538761 : CollatzResearch.WordTrace tailWord_7538761 prefixEnd_7538761 3871007932369684296617375 := by
  unfold tailWord_7538761
  simp only [CollatzResearch.WordTrace]
  refine ⟨274961202641363889719376137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183307468427575926479584091 274961202641363889719376137)
  ·
    refine ⟨206220901981022917289532103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274961202641363889719376137 206220901981022917289532103)
    ·
      refine ⟨309331352971534375934298155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206220901981022917289532103 309331352971534375934298155)
      ·
        refine ⟨463997029457301563901447233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309331352971534375934298155 463997029457301563901447233)
        ·
          refine ⟨347997772092976172926085425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463997029457301563901447233 347997772092976172926085425)
          ·
            refine ⟨260998329069732129694564069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347997772092976172926085425 260998329069732129694564069)
            ·
              refine ⟨48937186700574774317730763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260998329069732129694564069 48937186700574774317730763)
              ·
                refine ⟨73405780050862161476596145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48937186700574774317730763 73405780050862161476596145)
                ·
                  refine ⟨55054335038146621107447109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73405780050862161476596145 55054335038146621107447109)
                  ·
                    refine ⟨10322687819652491457646333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55054335038146621107447109 10322687819652491457646333)
                    ·
                      refine ⟨3871007932369684296617375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322687819652491457646333 3871007932369684296617375)
                      ·
                        rfl

theorem cell23_7538761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_7538761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538761 prefixEnd_7538761 := by exact prefixLift 7538761
  have htrace : WordTrace (prefixWord ++ tailWord_7538761) baseStart_7538761 baseEnd_7538761 := by
    simpa [prefixWord, tailWord_7538761, baseEnd_7538761] using wordTrace_append hprefix tailTrace_7538761
  have hstable : (prefixWord ++ tailWord_7538761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538761).length < 2 ^ (prefixWord ++ tailWord_7538761).sum := by decide
  have hdescent : baseEnd_7538761 < baseStart_7538761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538845 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_7538845 : Nat := 118140960795 + 7538845 * 2 ^ 59
def prefixEnd_7538845 : Nat := 4983230072969 + 3 ^ 40 * 7538845 * 2
def baseEnd_7538845 : Nat := 1290350354914887322655663

theorem tailTrace_7538845 : CollatzResearch.WordTrace tailWord_7538845 prefixEnd_7538845 1290350354914887322655663 := by
  unfold tailWord_7538845
  simp only [CollatzResearch.WordTrace]
  refine ⟨274964266373059572065433989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183309510915373048043622659 274964266373059572065433989)
  ·
    refine ⟨51555799944948669762268873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274964266373059572065433989 51555799944948669762268873)
    ·
      refine ⟨38666849958711502321701655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51555799944948669762268873 38666849958711502321701655)
      ·
        refine ⟨58000274938067253482552483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38666849958711502321701655 58000274938067253482552483)
        ·
          refine ⟨87000412407100880223828725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58000274938067253482552483 87000412407100880223828725)
          ·
            refine ⟨8156288663165707520983943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87000412407100880223828725 8156288663165707520983943)
            ·
              refine ⟨12234432994748561281475915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156288663165707520983943 12234432994748561281475915)
              ·
                refine ⟨18351649492122841922213873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234432994748561281475915 18351649492122841922213873)
                ·
                  refine ⟨13763737119092131441660405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18351649492122841922213873 13763737119092131441660405)
                  ·
                    refine ⟨1290350354914887322655663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13763737119092131441660405 1290350354914887322655663)
                    ·
                      rfl

theorem cell23_7538845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_7538845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538845 prefixEnd_7538845 := by exact prefixLift 7538845
  have htrace : WordTrace (prefixWord ++ tailWord_7538845) baseStart_7538845 baseEnd_7538845 := by
    simpa [prefixWord, tailWord_7538845, baseEnd_7538845] using wordTrace_append hprefix tailTrace_7538845
  have hstable : (prefixWord ++ tailWord_7538845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538845).length < 2 ^ (prefixWord ++ tailWord_7538845).sum := by decide
  have hdescent : baseEnd_7538845 < baseStart_7538845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538848 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_7538848 : Nat := 118140960795 + 7538848 * 2 ^ 59
def prefixEnd_7538848 : Nat := 4983230072969 + 3 ^ 40 * 7538848 * 2
def baseEnd_7538848 : Nat := 3871052605186625456229475

theorem tailTrace_7538848 : CollatzResearch.WordTrace tailWord_7538848 prefixEnd_7538848 3871052605186625456229475 := by
  unfold tailWord_7538848
  simp only [CollatzResearch.WordTrace]
  refine ⟨137482187896024351788896599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183309583861365802385195465 137482187896024351788896599)
  ·
    refine ⟨206223281844036527683344899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137482187896024351788896599 206223281844036527683344899)
    ·
      refine ⟨309334922766054791525017349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206223281844036527683344899 309334922766054791525017349)
      ·
        refine ⟨58000298018635273410940753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309334922766054791525017349 58000298018635273410940753)
        ·
          refine ⟨43500223513976455058205565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58000298018635273410940753 43500223513976455058205565)
          ·
            refine ⟨16312583817741170646827087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43500223513976455058205565 16312583817741170646827087)
            ·
              refine ⟨24468875726611755970240631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16312583817741170646827087 24468875726611755970240631)
              ·
                refine ⟨36703313589917633955360947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24468875726611755970240631 36703313589917633955360947)
                ·
                  refine ⟨55054970384876450933041421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36703313589917633955360947 55054970384876450933041421)
                  ·
                    refine ⟨20645613894328669099890533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55054970384876450933041421 20645613894328669099890533)
                    ·
                      refine ⟨3871052605186625456229475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20645613894328669099890533 3871052605186625456229475)
                      ·
                        rfl

theorem cell23_7538848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_7538848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538848 prefixEnd_7538848 := by exact prefixLift 7538848
  have htrace : WordTrace (prefixWord ++ tailWord_7538848) baseStart_7538848 baseEnd_7538848 := by
    simpa [prefixWord, tailWord_7538848, baseEnd_7538848] using wordTrace_append hprefix tailTrace_7538848
  have hstable : (prefixWord ++ tailWord_7538848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538848).length < 2 ^ (prefixWord ++ tailWord_7538848).sum := by decide
  have hdescent : baseEnd_7538848 < baseStart_7538848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538875 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 1, 4]
def baseStart_7538875 : Nat := 118140960795 + 7538875 * 2 ^ 59
def prefixEnd_7538875 : Nat := 4983230072969 + 3 ^ 40 * 7538875 * 2
def baseEnd_7538875 : Nat := 1290355489721432283530617

theorem tailTrace_7538875 : CollatzResearch.WordTrace tailWord_7538875 prefixEnd_7538875 1290355489721432283530617 := by
  unfold tailWord_7538875
  simp only [CollatzResearch.WordTrace]
  refine ⟨274965360562950887189026079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183310240375300591459350719 274965360562950887189026079)
  ·
    refine ⟨412448040844426330783539119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274965360562950887189026079 412448040844426330783539119)
    ·
      refine ⟨618672061266639496175308679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412448040844426330783539119 618672061266639496175308679)
      ·
        refine ⟨928008091899959244262963019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618672061266639496175308679 928008091899959244262963019)
        ·
          refine ⟨1392012137849938866394444529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928008091899959244262963019 1392012137849938866394444529)
          ·
            refine ⟨1044009103387454149795833397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392012137849938866394444529 1044009103387454149795833397)
            ·
              refine ⟨97875853442573826543359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1044009103387454149795833397 97875853442573826543359381)
              ·
                refine ⟨4587930630120648119219971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97875853442573826543359381 4587930630120648119219971)
                ·
                  refine ⟨6881895945180972178829957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587930630120648119219971 6881895945180972178829957)
                  ·
                    refine ⟨1290355489721432283530617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881895945180972178829957 1290355489721432283530617)
                    ·
                      rfl

theorem cell23_7538875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 4].length) (baseStart_7538875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538875 prefixEnd_7538875 := by exact prefixLift 7538875
  have htrace : WordTrace (prefixWord ++ tailWord_7538875) baseStart_7538875 baseEnd_7538875 := by
    simpa [prefixWord, tailWord_7538875, baseEnd_7538875] using wordTrace_append hprefix tailTrace_7538875
  have hstable : (prefixWord ++ tailWord_7538875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538875).length < 2 ^ (prefixWord ++ tailWord_7538875).sum := by decide
  have hdescent : baseEnd_7538875 < baseStart_7538875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538882 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7538882 : Nat := 118140960795 + 7538882 * 2 ^ 59
def prefixEnd_7538882 : Nat := 4983230072969 + 3 ^ 40 * 7538882 * 2
def baseEnd_7538882 : Nat := 3871070063528878323204319

theorem tailTrace_7538882 : CollatzResearch.WordTrace tailWord_7538882 prefixEnd_7538882 3871070063528878323204319 := by
  unfold tailWord_7538882
  simp only [CollatzResearch.WordTrace]
  refine ⟨68741403968481381846132725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183310410582617018256353933 68741403968481381846132725)
  ·
    refine ⟨6444506622045129548074943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68741403968481381846132725 6444506622045129548074943)
    ·
      refine ⟨9666759933067694322112415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444506622045129548074943 9666759933067694322112415)
      ·
        refine ⟨14500139899601541483168623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9666759933067694322112415 14500139899601541483168623)
        ·
          refine ⟨21750209849402312224752935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14500139899601541483168623 21750209849402312224752935)
          ·
            refine ⟨32625314774103468337129403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21750209849402312224752935 32625314774103468337129403)
            ·
              refine ⟨48937972161155202505694105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32625314774103468337129403 48937972161155202505694105)
              ·
                refine ⟨36703479120866401879270579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48937972161155202505694105 36703479120866401879270579)
                ·
                  refine ⟨55055218681299602818905869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36703479120866401879270579 55055218681299602818905869)
                  ·
                    refine ⟨20645707005487351057089701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55055218681299602818905869 20645707005487351057089701)
                    ·
                      refine ⟨3871070063528878323204319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20645707005487351057089701 3871070063528878323204319)
                      ·
                        rfl

theorem cell23_7538882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7538882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538882 prefixEnd_7538882 := by exact prefixLift 7538882
  have htrace : WordTrace (prefixWord ++ tailWord_7538882) baseStart_7538882 baseEnd_7538882 := by
    simpa [prefixWord, tailWord_7538882, baseEnd_7538882] using wordTrace_append hprefix tailTrace_7538882
  have hstable : (prefixWord ++ tailWord_7538882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538882).length < 2 ^ (prefixWord ++ tailWord_7538882).sum := by decide
  have hdescent : baseEnd_7538882 < baseStart_7538882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538891 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_7538891 : Nat := 118140960795 + 7538891 * 2 ^ 59
def prefixEnd_7538891 : Nat := 4983230072969 + 3 ^ 40 * 7538891 * 2
def baseEnd_7538891 : Nat := 3871074684854768787991777

theorem tailTrace_7538891 : CollatzResearch.WordTrace tailWord_7538891 prefixEnd_7538891 3871074684854768787991777 := by
  unfold tailWord_7538891
  simp only [CollatzResearch.WordTrace]
  refine ⟨274965944130892921921608527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183310629420595281281072351 274965944130892921921608527)
  ·
    refine ⟨412448916196339382882412791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274965944130892921921608527 412448916196339382882412791)
    ·
      refine ⟨618673374294509074323619187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412448916196339382882412791 618673374294509074323619187)
      ·
        refine ⟨928010061441763611485428781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618673374294509074323619187 928010061441763611485428781)
        ·
          refine ⟨348003773040661354307035793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 928010061441763611485428781 348003773040661354307035793)
          ·
            refine ⟨261002829780496015730276845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348003773040661354307035793 261002829780496015730276845)
            ·
              refine ⟨97876061167686005898853817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261002829780496015730276845 97876061167686005898853817)
              ·
                refine ⟨73407045875764504424140363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97876061167686005898853817 73407045875764504424140363)
                ·
                  refine ⟨110110568813646756636210545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73407045875764504424140363 110110568813646756636210545)
                  ·
                    refine ⟨82582926610235067477157909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110110568813646756636210545 82582926610235067477157909)
                    ·
                      refine ⟨3871074684854768787991777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82582926610235067477157909 3871074684854768787991777)
                      ·
                        rfl

theorem cell23_7538891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_7538891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538891 prefixEnd_7538891 := by exact prefixLift 7538891
  have htrace : WordTrace (prefixWord ++ tailWord_7538891) baseStart_7538891 baseEnd_7538891 := by
    simpa [prefixWord, tailWord_7538891, baseEnd_7538891] using wordTrace_append hprefix tailTrace_7538891
  have hstable : (prefixWord ++ tailWord_7538891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538891).length < 2 ^ (prefixWord ++ tailWord_7538891).sum := by decide
  have hdescent : baseEnd_7538891 < baseStart_7538891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538902 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_7538902 : Nat := 118140960795 + 7538902 * 2 ^ 59
def prefixEnd_7538902 : Nat := 4983230072969 + 3 ^ 40 * 7538902 * 2
def baseEnd_7538902 : Nat := 3871080333141968244954227

theorem tailTrace_7538902 : CollatzResearch.WordTrace tailWord_7538902 prefixEnd_7538902 3871080333141968244954227 := by
  unfold tailWord_7538902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17185396583365816925016185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183310896889235380533505973 17185396583365816925016185)
  ·
    refine ⟨12889047437524362693762139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17185396583365816925016185 12889047437524362693762139)
    ·
      refine ⟨19333571156286544040643209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12889047437524362693762139 19333571156286544040643209)
      ·
        refine ⟨14500178367214908030482407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19333571156286544040643209 14500178367214908030482407)
        ·
          refine ⟨21750267550822362045723611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14500178367214908030482407 21750267550822362045723611)
          ·
            refine ⟨32625401326233543068585417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21750267550822362045723611 32625401326233543068585417)
            ·
              refine ⟨24469050994675157301439063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32625401326233543068585417 24469050994675157301439063)
              ·
                refine ⟨36703576492012735952158595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24469050994675157301439063 36703576492012735952158595)
                ·
                  refine ⟨55055364738019103928237893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36703576492012735952158595 55055364738019103928237893)
                  ·
                    refine ⟨10322880888378581986544605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55055364738019103928237893 10322880888378581986544605)
                    ·
                      refine ⟨3871080333141968244954227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10322880888378581986544605 3871080333141968244954227)
                      ·
                        rfl

theorem cell23_7538902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_7538902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538902 prefixEnd_7538902 := by exact prefixLift 7538902
  have htrace : WordTrace (prefixWord ++ tailWord_7538902) baseStart_7538902 baseEnd_7538902 := by
    simpa [prefixWord, tailWord_7538902, baseEnd_7538902] using wordTrace_append hprefix tailTrace_7538902
  have hstable : (prefixWord ++ tailWord_7538902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538902).length < 2 ^ (prefixWord ++ tailWord_7538902).sum := by decide
  have hdescent : baseEnd_7538902 < baseStart_7538902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538909 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_7538909 : Nat := 118140960795 + 7538909 * 2 ^ 59
def prefixEnd_7538909 : Nat := 4983230072969 + 3 ^ 40 * 7538909 * 2
def baseEnd_7538909 : Nat := 1290361309168849905855565

theorem tailTrace_7538909 : CollatzResearch.WordTrace tailWord_7538909 prefixEnd_7538909 1290361309168849905855565 := by
  unfold tailWord_7538909
  simp only [CollatzResearch.WordTrace]
  refine ⟨274966600644827710995763781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183311067096551807330509187 274966600644827710995763781)
  ·
    refine ⟨51556237620905195811705709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274966600644827710995763781 51556237620905195811705709)
    ·
      refine ⟨19333589107839448429389641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51556237620905195811705709 19333589107839448429389641)
      ·
        refine ⟨14500191830879586322042231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19333589107839448429389641 14500191830879586322042231)
        ·
          refine ⟨21750287746319379483063347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14500191830879586322042231 21750287746319379483063347)
          ·
            refine ⟨32625431619479069224595021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21750287746319379483063347 32625431619479069224595021)
            ·
              refine ⟨12234536857304650959223133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32625431619479069224595021 12234536857304650959223133)
              ·
                refine ⟨4587951321489244109708675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12234536857304650959223133 4587951321489244109708675)
                ·
                  refine ⟨6881926982233866164563013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587951321489244109708675 6881926982233866164563013)
                  ·
                    refine ⟨1290361309168849905855565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881926982233866164563013 1290361309168849905855565)
                    ·
                      rfl

theorem cell23_7538909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_7538909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538909 prefixEnd_7538909 := by exact prefixLift 7538909
  have htrace : WordTrace (prefixWord ++ tailWord_7538909) baseStart_7538909 baseEnd_7538909 := by
    simpa [prefixWord, tailWord_7538909, baseEnd_7538909] using wordTrace_append hprefix tailTrace_7538909
  have hstable : (prefixWord ++ tailWord_7538909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538909).length < 2 ^ (prefixWord ++ tailWord_7538909).sum := by decide
  have hdescent : baseEnd_7538909 < baseStart_7538909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538942 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_7538942 : Nat := 118140960795 + 7538942 * 2 ^ 59
def prefixEnd_7538942 : Nat := 4983230072969 + 3 ^ 40 * 7538942 * 2
def baseEnd_7538942 : Nat := 3871100872368148088454043

theorem tailTrace_7538942 : CollatzResearch.WordTrace tailWord_7538942 prefixEnd_7538942 3871100872368148088454043 := by
  unfold tailWord_7538942
  simp only [CollatzResearch.WordTrace]
  refine ⟨34370975531713519703964385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183311869502472105087810053 34370975531713519703964385)
  ·
    refine ⟨25778231648785139777973289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34370975531713519703964385 25778231648785139777973289)
    ·
      refine ⟨19333673736588854833479967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25778231648785139777973289 19333673736588854833479967)
      ·
        refine ⟨29000510604883282250219951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19333673736588854833479967 29000510604883282250219951)
        ·
          refine ⟨43500765907324923375329927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29000510604883282250219951 43500765907324923375329927)
          ·
            refine ⟨65251148860987385062994891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43500765907324923375329927 65251148860987385062994891)
            ·
              refine ⟨97876723291481077594492337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65251148860987385062994891 97876723291481077594492337)
              ·
                refine ⟨73407542468610808195869253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97876723291481077594492337 73407542468610808195869253)
                ·
                  refine ⟨13763914212864526536725485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73407542468610808195869253 13763914212864526536725485)
                  ·
                    refine ⟨5161467829824197451272057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13763914212864526536725485 5161467829824197451272057)
                    ·
                      refine ⟨3871100872368148088454043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161467829824197451272057 3871100872368148088454043)
                      ·
                        rfl

theorem cell23_7538942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_7538942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538942 prefixEnd_7538942 := by exact prefixLift 7538942
  have htrace : WordTrace (prefixWord ++ tailWord_7538942) baseStart_7538942 baseEnd_7538942 := by
    simpa [prefixWord, tailWord_7538942, baseEnd_7538942] using wordTrace_append hprefix tailTrace_7538942
  have hstable : (prefixWord ++ tailWord_7538942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538942).length < 2 ^ (prefixWord ++ tailWord_7538942).sum := by decide
  have hdescent : baseEnd_7538942 < baseStart_7538942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538952 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_7538952 : Nat := 118140960795 + 7538952 * 2 ^ 59
def prefixEnd_7538952 : Nat := 4983230072969 + 3 ^ 40 * 7538952 * 2
def baseEnd_7538952 : Nat := 1290368669058231016442999

theorem tailTrace_7538952 : CollatzResearch.WordTrace tailWord_7538952 prefixEnd_7538952 1290368669058231016442999 := by
  unfold tailWord_7538952
  simp only [CollatzResearch.WordTrace]
  refine ⟨137484084491835964669789555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183312112655781286226386073 137484084491835964669789555)
  ·
    refine ⟨206226126737753947004684333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137484084491835964669789555 206226126737753947004684333)
    ·
      refine ⟨77334797526657730126756625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206226126737753947004684333 77334797526657730126756625)
      ·
        refine ⟨58001098144993297595067469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77334797526657730126756625 58001098144993297595067469)
        ·
          refine ⟨21750411804372486598150301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58001098144993297595067469 21750411804372486598150301)
          ·
            refine ⟨8156404426639682474306363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21750411804372486598150301 8156404426639682474306363)
            ·
              refine ⟨12234606639959523711459545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156404426639682474306363 12234606639959523711459545)
              ·
                refine ⟨9175954979969642783594659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12234606639959523711459545 9175954979969642783594659)
                ·
                  refine ⟨13763932469954464175391989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9175954979969642783594659 13763932469954464175391989)
                  ·
                    refine ⟨1290368669058231016442999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13763932469954464175391989 1290368669058231016442999)
                    ·
                      rfl

theorem cell23_7538952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_7538952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538952 prefixEnd_7538952 := by exact prefixLift 7538952
  have htrace : WordTrace (prefixWord ++ tailWord_7538952) baseStart_7538952 baseEnd_7538952 := by
    simpa [prefixWord, tailWord_7538952, baseEnd_7538952] using wordTrace_append hprefix tailTrace_7538952
  have hstable : (prefixWord ++ tailWord_7538952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538952).length < 2 ^ (prefixWord ++ tailWord_7538952).sum := by decide
  have hdescent : baseEnd_7538952 < baseStart_7538952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538975 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_7538975 : Nat := 118140960795 + 7538975 * 2 ^ 59
def prefixEnd_7538975 : Nat := 4983230072969 + 3 ^ 40 * 7538975 * 2
def baseEnd_7538975 : Nat := 3871117817229746459341391

theorem tailTrace_7538975 : CollatzResearch.WordTrace tailWord_7538975 prefixEnd_7538975 3871117817229746459341391 := by
  unfold tailWord_7538975
  simp only [CollatzResearch.WordTrace]
  refine ⟨274969007862588604267666379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183312671908392402845110919 274969007862588604267666379)
  ·
    refine ⟨412453511793882906401499569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274969007862588604267666379 412453511793882906401499569)
    ·
      refine ⟨309340133845412179801124677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412453511793882906401499569 309340133845412179801124677)
      ·
        refine ⟨58001275096014783712710877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309340133845412179801124677 58001275096014783712710877)
        ·
          refine ⟨21750478161005543892266579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58001275096014783712710877 21750478161005543892266579)
          ·
            refine ⟨32625717241508315838399869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21750478161005543892266579 32625717241508315838399869)
            ·
              refine ⟨12234643965565618439399951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32625717241508315838399869 12234643965565618439399951)
              ·
                refine ⟨18351965948348427659099927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234643965565618439399951 18351965948348427659099927)
                ·
                  refine ⟨27527948922522641488649891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18351965948348427659099927 27527948922522641488649891)
                  ·
                    refine ⟨41291923383783962232974837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27527948922522641488649891 41291923383783962232974837)
                    ·
                      refine ⟨3871117817229746459341391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41291923383783962232974837 3871117817229746459341391)
                      ·
                        rfl

theorem cell23_7538975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_7538975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538975 prefixEnd_7538975 := by exact prefixLift 7538975
  have htrace : WordTrace (prefixWord ++ tailWord_7538975) baseStart_7538975 baseEnd_7538975 := by
    simpa [prefixWord, tailWord_7538975, baseEnd_7538975] using wordTrace_append hprefix tailTrace_7538975
  have hstable : (prefixWord ++ tailWord_7538975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538975).length < 2 ^ (prefixWord ++ tailWord_7538975).sum := by decide
  have hdescent : baseEnd_7538975 < baseStart_7538975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7538978 : List Nat := [3, 3, 1, 1, 3, 12]
def baseStart_7538978 : Nat := 118140960795 + 7538978 * 2 ^ 59
def prefixEnd_7538978 : Nat := 4983230072969 + 3 ^ 40 * 7538978 * 2
def baseEnd_7538978 : Nat := 15930532336097571800839

theorem tailTrace_7538978 : CollatzResearch.WordTrace tailWord_7538978 prefixEnd_7538978 15930532336097571800839 := by
  unfold tailWord_7538978
  simp only [CollatzResearch.WordTrace]
  refine ⟨68742279320394433945006397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183312744854385157186683725 68742279320394433945006397)
  ·
    refine ⟨25778354745147912729377399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68742279320394433945006397 25778354745147912729377399)
    ·
      refine ⟨38667532117721869094066099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25778354745147912729377399 38667532117721869094066099)
      ·
        refine ⟨58001298176582803641099149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38667532117721869094066099 58001298176582803641099149)
        ·
          refine ⟨21750486816218551365412181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58001298176582803641099149 21750486816218551365412181)
          ·
            refine ⟨15930532336097571800839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21750486816218551365412181 15930532336097571800839)
            ·
              rfl

theorem cell23_7538978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 12].length) (baseStart_7538978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7538978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7538978 prefixEnd_7538978 := by exact prefixLift 7538978
  have htrace : WordTrace (prefixWord ++ tailWord_7538978) baseStart_7538978 baseEnd_7538978 := by
    simpa [prefixWord, tailWord_7538978, baseEnd_7538978] using wordTrace_append hprefix tailTrace_7538978
  have hstable : (prefixWord ++ tailWord_7538978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7538978).length < 2 ^ (prefixWord ++ tailWord_7538978).sum := by decide
  have hdescent : baseEnd_7538978 < baseStart_7538978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7538978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539068 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 9]
def baseStart_7539068 : Nat := 118140960795 + 7539068 * 2 ^ 59
def prefixEnd_7539068 : Nat := 4983230072969 + 3 ^ 40 * 7539068 * 2
def baseEnd_7539068 : Nat := 430129507881179399497607

theorem tailTrace_7539068 : CollatzResearch.WordTrace tailWord_7539068 prefixEnd_7539068 430129507881179399497607 := by
  unfold tailWord_7539068
  simp only [CollatzResearch.WordTrace]
  refine ⟨137486199925625840575400929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183314933234167787433867905 137486199925625840575400929)
  ·
    refine ⟨103114649944219380431550697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137486199925625840575400929 103114649944219380431550697)
    ·
      refine ⟨77335987458164535323663023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103114649944219380431550697 77335987458164535323663023)
      ·
        refine ⟨116003981187246802985494535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77335987458164535323663023 116003981187246802985494535)
        ·
          refine ⟨174005971780870204478241803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116003981187246802985494535 174005971780870204478241803)
          ·
            refine ⟨261008957671305306717362705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174005971780870204478241803 261008957671305306717362705)
            ·
              refine ⟨195756718253478980038022029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261008957671305306717362705 195756718253478980038022029)
              ·
                refine ⟨73408769345054617514258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195756718253478980038022029 73408769345054617514258261)
                ·
                  refine ⟨430129507881179399497607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73408769345054617514258261 430129507881179399497607)
                  ·
                    rfl

theorem cell23_7539068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_7539068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539068 prefixEnd_7539068 := by exact prefixLift 7539068
  have htrace : WordTrace (prefixWord ++ tailWord_7539068) baseStart_7539068 baseEnd_7539068 := by
    simpa [prefixWord, tailWord_7539068, baseEnd_7539068] using wordTrace_append hprefix tailTrace_7539068
  have hstable : (prefixWord ++ tailWord_7539068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539068).length < 2 ^ (prefixWord ++ tailWord_7539068).sum := by decide
  have hdescent : baseEnd_7539068 < baseStart_7539068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539095 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_7539095 : Nat := 118140960795 + 7539095 * 2 ^ 59
def prefixEnd_7539095 : Nat := 4983230072969 + 3 ^ 40 * 7539095 * 2
def baseEnd_7539095 : Nat := 3871179434908285989840839

theorem tailTrace_7539095 : CollatzResearch.WordTrace tailWord_7539095 prefixEnd_7539095 3871179434908285989840839 := by
  unfold tailWord_7539095
  simp only [CollatzResearch.WordTrace]
  refine ⟨274973384622153864762034739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183315589748102576508023159 274973384622153864762034739)
  ·
    refine ⟨412460076933230797143052109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274973384622153864762034739 412460076933230797143052109)
    ·
      refine ⟨154672528849961548928644541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412460076933230797143052109 154672528849961548928644541)
      ·
        refine ⟨58002198318735580848241703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154672528849961548928644541 58002198318735580848241703)
        ·
          refine ⟨87003297478103371272362555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58002198318735580848241703 87003297478103371272362555)
          ·
            refine ⟨130504946217155056908543833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87003297478103371272362555 130504946217155056908543833)
            ·
              refine ⟨97878709662866292681407875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130504946217155056908543833 97878709662866292681407875)
              ·
                refine ⟨146818064494299439022111813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97878709662866292681407875 146818064494299439022111813)
                ·
                  refine ⟨27528387092681144816645965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146818064494299439022111813 27528387092681144816645965)
                  ·
                    refine ⟨10323145159755429306242237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27528387092681144816645965 10323145159755429306242237)
                    ·
                      refine ⟨3871179434908285989840839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323145159755429306242237 3871179434908285989840839)
                      ·
                        rfl

theorem cell23_7539095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_7539095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539095 prefixEnd_7539095 := by exact prefixLift 7539095
  have htrace : WordTrace (prefixWord ++ tailWord_7539095) baseStart_7539095 baseEnd_7539095 := by
    simpa [prefixWord, tailWord_7539095, baseEnd_7539095] using wordTrace_append hprefix tailTrace_7539095
  have hstable : (prefixWord ++ tailWord_7539095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539095).length < 2 ^ (prefixWord ++ tailWord_7539095).sum := by decide
  have hdescent : baseEnd_7539095 < baseStart_7539095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539132 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_7539132 : Nat := 118140960795 + 7539132 * 2 ^ 59
def prefixEnd_7539132 : Nat := 4983230072969 + 3 ^ 40 * 7539132 * 2
def baseEnd_7539132 : Nat := 1290399477897500781692723

theorem tailTrace_7539132 : CollatzResearch.WordTrace tailWord_7539132 prefixEnd_7539132 1290399477897500781692723 := by
  unfold tailWord_7539132
  simp only [CollatzResearch.WordTrace]
  refine ⟨137487367061509910040565825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183316489415346546720754433 137487367061509910040565825)
  ·
    refine ⟨103115525296132432530424369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137487367061509910040565825 103115525296132432530424369)
    ·
      refine ⟨77336643972099324397818277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103115525296132432530424369 77336643972099324397818277)
      ·
        refine ⟨14500620744768623324590927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77336643972099324397818277 14500620744768623324590927)
        ·
          refine ⟨21750931117152934986886391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14500620744768623324590927 21750931117152934986886391)
          ·
            refine ⟨32626396675729402480329587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21750931117152934986886391 32626396675729402480329587)
            ·
              refine ⟨48939595013594103720494381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32626396675729402480329587 48939595013594103720494381)
              ·
                refine ⟨18352348130097788895185393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48939595013594103720494381 18352348130097788895185393)
                ·
                  refine ⟨13764261097573341671389045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18352348130097788895185393 13764261097573341671389045)
                  ·
                    refine ⟨1290399477897500781692723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13764261097573341671389045 1290399477897500781692723)
                    ·
                      rfl

theorem cell23_7539132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_7539132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539132 prefixEnd_7539132 := by exact prefixLift 7539132
  have htrace : WordTrace (prefixWord ++ tailWord_7539132) baseStart_7539132 baseEnd_7539132 := by
    simpa [prefixWord, tailWord_7539132, baseEnd_7539132] using wordTrace_append hprefix tailTrace_7539132
  have hstable : (prefixWord ++ tailWord_7539132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539132).length < 2 ^ (prefixWord ++ tailWord_7539132).sum := by decide
  have hdescent : baseEnd_7539132 < baseStart_7539132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539162 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_7539162 : Nat := 118140960795 + 7539162 * 2 ^ 59
def prefixEnd_7539162 : Nat := 4983230072969 + 3 ^ 40 * 7539162 * 2
def baseEnd_7539162 : Nat := 1290404612704045742567677

theorem tailTrace_7539162 : CollatzResearch.WordTrace tailWord_7539162 prefixEnd_7539162 1290404612704045742567677 := by
  unfold tailWord_7539162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68743957078227783801180935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183317218875274090136482493 68743957078227783801180935)
  ·
    refine ⟨103115935617341675701771403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68743957078227783801180935 103115935617341675701771403)
    ·
      refine ⟨154673903426012513552657105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103115935617341675701771403 154673903426012513552657105)
      ·
        refine ⟨116005427569509385164492829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154673903426012513552657105 116005427569509385164492829)
        ·
          refine ⟨43502035338566019436684811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116005427569509385164492829 43502035338566019436684811)
          ·
            refine ⟨65253053007849029155027217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43502035338566019436684811 65253053007849029155027217)
            ·
              refine ⟨48939789755886771866270413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65253053007849029155027217 48939789755886771866270413)
              ·
                refine ⟨18352421158457539449851405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48939789755886771866270413 18352421158457539449851405)
                ·
                  refine ⟨6882157934421577293694277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18352421158457539449851405 6882157934421577293694277)
                  ·
                    refine ⟨1290404612704045742567677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882157934421577293694277 1290404612704045742567677)
                    ·
                      rfl

theorem cell23_7539162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_7539162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539162 prefixEnd_7539162 := by exact prefixLift 7539162
  have htrace : WordTrace (prefixWord ++ tailWord_7539162) baseStart_7539162 baseEnd_7539162 := by
    simpa [prefixWord, tailWord_7539162, baseEnd_7539162] using wordTrace_append hprefix tailTrace_7539162
  have hstable : (prefixWord ++ tailWord_7539162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539162).length < 2 ^ (prefixWord ++ tailWord_7539162).sum := by decide
  have hdescent : baseEnd_7539162 < baseStart_7539162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539186 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7539186 : Nat := 118140960795 + 7539186 * 2 ^ 59
def prefixEnd_7539186 : Nat := 4983230072969 + 3 ^ 40 * 7539186 * 2
def baseEnd_7539186 : Nat := 3871226161647845133802921

theorem tailTrace_7539186 : CollatzResearch.WordTrace tailWord_7539186 prefixEnd_7539186 3871226161647845133802921 := by
  unfold tailWord_7539186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68744175916206046825899353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183317802443216124869064941 68744175916206046825899353)
  ·
    refine ⟨51558131937154535119424515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68744175916206046825899353 51558131937154535119424515)
    ·
      refine ⟨77337197905731802679136773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51558131937154535119424515 77337197905731802679136773)
      ·
        refine ⟨14500724607324713002338145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77337197905731802679136773 14500724607324713002338145)
        ·
          refine ⟨10875543455493534751753609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14500724607324713002338145 10875543455493534751753609)
          ·
            refine ⟨8156657591620151063815207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10875543455493534751753609 8156657591620151063815207)
            ·
              refine ⟨12234986387430226595722811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156657591620151063815207 12234986387430226595722811)
              ·
                refine ⟨18352479581145339893584217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234986387430226595722811 18352479581145339893584217)
                ·
                  refine ⟨13764359685859004920188163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18352479581145339893584217 13764359685859004920188163)
                  ·
                    refine ⟨20646539528788507380282245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13764359685859004920188163 20646539528788507380282245)
                    ·
                      refine ⟨3871226161647845133802921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20646539528788507380282245 3871226161647845133802921)
                      ·
                        rfl

theorem cell23_7539186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7539186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539186 prefixEnd_7539186 := by exact prefixLift 7539186
  have htrace : WordTrace (prefixWord ++ tailWord_7539186) baseStart_7539186 baseEnd_7539186 := by
    simpa [prefixWord, tailWord_7539186, baseEnd_7539186] using wordTrace_append hprefix tailTrace_7539186
  have hstable : (prefixWord ++ tailWord_7539186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539186).length < 2 ^ (prefixWord ++ tailWord_7539186).sum := by decide
  have hdescent : baseEnd_7539186 < baseStart_7539186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539213 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_7539213 : Nat := 118140960795 + 7539213 * 2 ^ 59
def prefixEnd_7539213 : Nat := 4983230072969 + 3 ^ 40 * 7539213 * 2
def baseEnd_7539213 : Nat := 1290413341875172176055099

theorem tailTrace_7539213 : CollatzResearch.WordTrace tailWord_7539213 prefixEnd_7539213 1290413341875172176055099 := by
  unfold tailWord_7539213
  simp only [CollatzResearch.WordTrace]
  refine ⟨274977688435726370914830293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183318458957150913943220195 274977688435726370914830293)
  ·
    refine ⟨6444789572712336818316335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 274977688435726370914830293 6444789572712336818316335)
    ·
      refine ⟨9667184359068505227474503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444789572712336818316335 9667184359068505227474503)
      ·
        refine ⟨14500776538602757841211755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9667184359068505227474503 14500776538602757841211755)
        ·
          refine ⟨21751164807904136761817633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14500776538602757841211755 21751164807904136761817633)
          ·
            refine ⟨16313373605928102571363225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21751164807904136761817633 16313373605928102571363225)
            ·
              refine ⟨12235030204446076928522419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16313373605928102571363225 12235030204446076928522419)
              ·
                refine ⟨18352545306669115392783629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12235030204446076928522419 18352545306669115392783629)
                ·
                  refine ⟨6882204490000918272293861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18352545306669115392783629 6882204490000918272293861)
                  ·
                    refine ⟨1290413341875172176055099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882204490000918272293861 1290413341875172176055099)
                    ·
                      rfl

theorem cell23_7539213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_7539213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539213 prefixEnd_7539213 := by exact prefixLift 7539213
  have htrace : WordTrace (prefixWord ++ tailWord_7539213) baseStart_7539213 baseEnd_7539213 := by
    simpa [prefixWord, tailWord_7539213, baseEnd_7539213] using wordTrace_append hprefix tailTrace_7539213
  have hstable : (prefixWord ++ tailWord_7539213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539213).length < 2 ^ (prefixWord ++ tailWord_7539213).sum := by decide
  have hdescent : baseEnd_7539213 < baseStart_7539213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539219 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 3]
def baseStart_7539219 : Nat := 118140960795 + 7539219 * 2 ^ 59
def prefixEnd_7539219 : Nat := 4983230072969 + 3 ^ 40 * 7539219 * 2
def baseEnd_7539219 : Nat := 3871243106509443504690269

theorem tailTrace_7539219 : CollatzResearch.WordTrace tailWord_7539219 prefixEnd_7539219 3871243106509443504690269 := by
  unfold tailWord_7539219
  simp only [CollatzResearch.WordTrace]
  refine ⟨274977907273704633939548711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183318604849136422626365807 274977907273704633939548711)
  ·
    refine ⟨412466860910556950909323067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274977907273704633939548711 412466860910556950909323067)
    ·
      refine ⟨618700291365835426363984601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412466860910556950909323067 618700291365835426363984601)
      ·
        refine ⟨464025218524376569772988451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618700291365835426363984601 464025218524376569772988451)
        ·
          refine ⟨696037827786564854659482677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464025218524376569772988451 696037827786564854659482677)
          ·
            refine ⟨65253546354990455124326501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 696037827786564854659482677 65253546354990455124326501)
            ·
              refine ⟨12235039941560710335811219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65253546354990455124326501 12235039941560710335811219)
              ·
                refine ⟨18352559912341065503716829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12235039941560710335811219 18352559912341065503716829)
                ·
                  refine ⟨6882209967127899563893811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18352559912341065503716829 6882209967127899563893811)
                  ·
                    refine ⟨10323314950691849345840717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882209967127899563893811 10323314950691849345840717)
                    ·
                      refine ⟨3871243106509443504690269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323314950691849345840717 3871243106509443504690269)
                      ·
                        rfl

theorem cell23_7539219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_7539219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539219 prefixEnd_7539219 := by exact prefixLift 7539219
  have htrace : WordTrace (prefixWord ++ tailWord_7539219) baseStart_7539219 baseEnd_7539219 := by
    simpa [prefixWord, tailWord_7539219, baseEnd_7539219] using wordTrace_append hprefix tailTrace_7539219
  have hstable : (prefixWord ++ tailWord_7539219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539219).length < 2 ^ (prefixWord ++ tailWord_7539219).sum := by decide
  have hdescent : baseEnd_7539219 < baseStart_7539219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539229 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_7539229 : Nat := 118140960795 + 7539229 * 2 ^ 59
def prefixEnd_7539229 : Nat := 4983230072969 + 3 ^ 40 * 7539229 * 2
def baseEnd_7539229 : Nat := 3871248241315988465565223

theorem tailTrace_7539229 : CollatzResearch.WordTrace tailWord_7539229 prefixEnd_7539229 3871248241315988465565223 := by
  unfold tailWord_7539229
  simp only [CollatzResearch.WordTrace]
  refine ⟨274978272003668405647412741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183318848002445603764941827 274978272003668405647412741)
  ·
    refine ⟨51558426000687826058889889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274978272003668405647412741 51558426000687826058889889)
    ·
      refine ⟨38668819500515869544167417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51558426000687826058889889 38668819500515869544167417)
      ·
        refine ⟨29001614625386902158125563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38668819500515869544167417 29001614625386902158125563)
        ·
          refine ⟨43502421938080353237188345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29001614625386902158125563 43502421938080353237188345)
          ·
            refine ⟨32626816453560264927891259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43502421938080353237188345 32626816453560264927891259)
            ·
              refine ⟨48940224680340397391836889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32626816453560264927891259 48940224680340397391836889)
              ·
                refine ⟨36705168510255298043877667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48940224680340397391836889 36705168510255298043877667)
                ·
                  refine ⟨55057752765382947065816501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36705168510255298043877667 55057752765382947065816501)
                  ·
                    refine ⟨5161664321754651287420297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55057752765382947065816501 5161664321754651287420297)
                    ·
                      refine ⟨3871248241315988465565223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161664321754651287420297 3871248241315988465565223)
                      ·
                        rfl

theorem cell23_7539229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_7539229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539229 prefixEnd_7539229 := by exact prefixLift 7539229
  have htrace : WordTrace (prefixWord ++ tailWord_7539229) baseStart_7539229 baseEnd_7539229 := by
    simpa [prefixWord, tailWord_7539229, baseEnd_7539229] using wordTrace_append hprefix tailTrace_7539229
  have hstable : (prefixWord ++ tailWord_7539229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539229).length < 2 ^ (prefixWord ++ tailWord_7539229).sum := by decide
  have hdescent : baseEnd_7539229 < baseStart_7539229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539270 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7539270 : Nat := 118140960795 + 7539270 * 2 ^ 59
def prefixEnd_7539270 : Nat := 4983230072969 + 3 ^ 40 * 7539270 * 2
def baseEnd_7539270 : Nat := 3871269294022822805152535

theorem tailTrace_7539270 : CollatzResearch.WordTrace tailWord_7539270 prefixEnd_7539270 3871269294022822805152535 := by
  unfold tailWord_7539270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8593117731141245926551727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183319844931013246433103509 8593117731141245926551727)
  ·
    refine ⟨12889676596711868889827591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8593117731141245926551727 12889676596711868889827591)
    ·
      refine ⟨19334514895067803334741387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12889676596711868889827591 19334514895067803334741387)
      ·
        refine ⟨29001772342601705002112081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19334514895067803334741387 29001772342601705002112081)
        ·
          refine ⟨21751329256951278751584061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29001772342601705002112081 21751329256951278751584061)
          ·
            refine ⟨8156748471356729531844023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21751329256951278751584061 8156748471356729531844023)
            ·
              refine ⟨12235122707035094297766035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156748471356729531844023 12235122707035094297766035)
              ·
                refine ⟨18352684060552641446649053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12235122707035094297766035 18352684060552641446649053)
                ·
                  refine ⟨6882256522707240542493395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18352684060552641446649053 6882256522707240542493395)
                  ·
                    refine ⟨10323384784060860813740093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882256522707240542493395 10323384784060860813740093)
                    ·
                      refine ⟨3871269294022822805152535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323384784060860813740093 3871269294022822805152535)
                      ·
                        rfl

theorem cell23_7539270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7539270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539270 prefixEnd_7539270 := by exact prefixLift 7539270
  have htrace : WordTrace (prefixWord ++ tailWord_7539270) baseStart_7539270 baseEnd_7539270 := by
    simpa [prefixWord, tailWord_7539270, baseEnd_7539270] using wordTrace_append hprefix tailTrace_7539270
  have hstable : (prefixWord ++ tailWord_7539270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539270).length < 2 ^ (prefixWord ++ tailWord_7539270).sum := by decide
  have hdescent : baseEnd_7539270 < baseStart_7539270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539282 : List Nat := [3, 2, 2, 1, 2, 1, 4, 8]
def baseStart_7539282 : Nat := 118140960795 + 7539282 * 2 ^ 59
def prefixEnd_7539282 : Nat := 4983230072969 + 3 ^ 40 * 7539282 * 2
def baseEnd_7539282 : Nat := 143380572436691731785277

theorem tailTrace_7539282 : CollatzResearch.WordTrace tailWord_7539282 prefixEnd_7539282 143380572436691731785277 := by
  unfold tailWord_7539282
  simp only [CollatzResearch.WordTrace]
  refine ⟨68745051268119098924773025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183320136714984263799394733 68745051268119098924773025)
  ·
    refine ⟨51558788451089324193579769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68745051268119098924773025 51558788451089324193579769)
    ·
      refine ⟨38669091338316993145184827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51558788451089324193579769 38669091338316993145184827)
      ·
        refine ⟨58003637007475489717777241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38669091338316993145184827 58003637007475489717777241)
        ·
          refine ⟨43502727755606617288332931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58003637007475489717777241 43502727755606617288332931)
          ·
            refine ⟨65254091633409925932499397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43502727755606617288332931 65254091633409925932499397)
            ·
              refine ⟨12235142181264361112343637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65254091633409925932499397 12235142181264361112343637)
              ·
                refine ⟨143380572436691731785277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12235142181264361112343637 143380572436691731785277)
                ·
                  rfl

theorem cell23_7539282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_7539282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539282 prefixEnd_7539282 := by exact prefixLift 7539282
  have htrace : WordTrace (prefixWord ++ tailWord_7539282) baseStart_7539282 baseEnd_7539282 := by
    simpa [prefixWord, tailWord_7539282, baseEnd_7539282] using wordTrace_append hprefix tailTrace_7539282
  have hstable : (prefixWord ++ tailWord_7539282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539282).length < 2 ^ (prefixWord ++ tailWord_7539282).sum := by decide
  have hdescent : baseEnd_7539282 < baseStart_7539282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539309 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_7539309 : Nat := 118140960795 + 7539309 * 2 ^ 59
def prefixEnd_7539309 : Nat := 4983230072969 + 3 ^ 40 * 7539309 * 2
def baseEnd_7539309 : Nat := 3871289319768348152564855

theorem tailTrace_7539309 : CollatzResearch.WordTrace tailWord_7539309 prefixEnd_7539309 3871289319768348152564855 := by
  unfold tailWord_7539309
  simp only [CollatzResearch.WordTrace]
  refine ⟨274981189843378579310324981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183320793228919052873549987 274981189843378579310324981)
  ·
    refine ⟨25779486547816741810342967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274981189843378579310324981 25779486547816741810342967)
    ·
      refine ⟨38669229821725112715514451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25779486547816741810342967 38669229821725112715514451)
      ·
        refine ⟨58003844732587669073271677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38669229821725112715514451 58003844732587669073271677)
        ·
          refine ⟨21751441774720375902476879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58003844732587669073271677 21751441774720375902476879)
          ·
            refine ⟨32627162662080563853715319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21751441774720375902476879 32627162662080563853715319)
            ·
              refine ⟨48940743993120845780572979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32627162662080563853715319 48940743993120845780572979)
              ·
                refine ⟨73411115989681268670859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48940743993120845780572979 73411115989681268670859469)
                ·
                  refine ⟨27529168496130475751572301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73411115989681268670859469 27529168496130475751572301)
                  ·
                    refine ⟨10323438186048928406839613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27529168496130475751572301 10323438186048928406839613)
                    ·
                      refine ⟨3871289319768348152564855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323438186048928406839613 3871289319768348152564855)
                      ·
                        rfl

theorem cell23_7539309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_7539309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539309 prefixEnd_7539309 := by exact prefixLift 7539309
  have htrace : WordTrace (prefixWord ++ tailWord_7539309) baseStart_7539309 baseEnd_7539309 := by
    simpa [prefixWord, tailWord_7539309, baseEnd_7539309] using wordTrace_append hprefix tailTrace_7539309
  have hstable : (prefixWord ++ tailWord_7539309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539309).length < 2 ^ (prefixWord ++ tailWord_7539309).sum := by decide
  have hdescent : baseEnd_7539309 < baseStart_7539309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539377 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7539377 : Nat := 118140960795 + 7539377 * 2 ^ 59
def prefixEnd_7539377 : Nat := 4983230072969 + 3 ^ 40 * 7539377 * 2
def baseEnd_7539377 : Nat := 3871324236452853886514543

theorem tailTrace_7539377 : CollatzResearch.WordTrace tailWord_7539377 prefixEnd_7539377 3871324236452853886514543 := by
  unfold tailWord_7539377
  simp only [CollatzResearch.WordTrace]
  refine ⟨274983670007132226923800385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183322446671421484615866923 274983670007132226923800385)
  ·
    refine ⟨206237752505349170192850289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274983670007132226923800385 206237752505349170192850289)
    ·
      refine ⟨154678314379011877644637717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206237752505349170192850289 154678314379011877644637717)
      ·
        refine ⟨7250545986516181764592393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154678314379011877644637717 7250545986516181764592393)
        ·
          refine ⟨5437909489887136323444295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250545986516181764592393 5437909489887136323444295)
          ·
            refine ⟨8156864234830704485166443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437909489887136323444295 8156864234830704485166443)
            ·
              refine ⟨12235296352246056727749665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156864234830704485166443 12235296352246056727749665)
              ·
                refine ⟨9176472264184542545812249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12235296352246056727749665 9176472264184542545812249)
                ·
                  refine ⟨6882354198138406909359187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9176472264184542545812249 6882354198138406909359187)
                  ·
                    refine ⟨10323531297207610364038781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882354198138406909359187 10323531297207610364038781)
                    ·
                      refine ⟨3871324236452853886514543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323531297207610364038781 3871324236452853886514543)
                      ·
                        rfl

theorem cell23_7539377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7539377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539377 prefixEnd_7539377 := by exact prefixLift 7539377
  have htrace : WordTrace (prefixWord ++ tailWord_7539377) baseStart_7539377 baseEnd_7539377 := by
    simpa [prefixWord, tailWord_7539377, baseEnd_7539377] using wordTrace_append hprefix tailTrace_7539377
  have hstable : (prefixWord ++ tailWord_7539377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539377).length < 2 ^ (prefixWord ++ tailWord_7539377).sum := by decide
  have hdescent : baseEnd_7539377 < baseStart_7539377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539383 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_7539383 : Nat := 118140960795 + 7539383 * 2 ^ 59
def prefixEnd_7539383 : Nat := 4983230072969 + 3 ^ 40 * 7539383 * 2
def baseEnd_7539383 : Nat := 3871327317336780863039515

theorem tailTrace_7539383 : CollatzResearch.WordTrace tailWord_7539383 prefixEnd_7539383 3871327317336780863039515 := by
  unfold tailWord_7539383
  simp only [CollatzResearch.WordTrace]
  refine ⟨274983888845110489948518803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183322592563406993299012535 274983888845110489948518803)
  ·
    refine ⟨412475833267665734922778205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274983888845110489948518803 412475833267665734922778205)
    ·
      refine ⟨154678437475374650596041827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412475833267665734922778205 154678437475374650596041827)
      ·
        refine ⟨232017656213061975894062741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154678437475374650596041827 232017656213061975894062741)
        ·
          refine ⟨10875827634987280120034191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232017656213061975894062741 10875827634987280120034191)
          ·
            refine ⟨16313741452480920180051287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10875827634987280120034191 16313741452480920180051287)
            ·
              refine ⟨24470612178721380270076931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16313741452480920180051287 24470612178721380270076931)
              ·
                refine ⟨36705918268082070405115397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24470612178721380270076931 36705918268082070405115397)
                ·
                  refine ⟨6882359675265388200959137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36705918268082070405115397 6882359675265388200959137)
                  ·
                    refine ⟨5161769756449041150719353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6882359675265388200959137 5161769756449041150719353)
                    ·
                      refine ⟨3871327317336780863039515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161769756449041150719353 3871327317336780863039515)
                      ·
                        rfl

theorem cell23_7539383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_7539383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539383 prefixEnd_7539383 := by exact prefixLift 7539383
  have htrace : WordTrace (prefixWord ++ tailWord_7539383) baseStart_7539383 baseEnd_7539383 := by
    simpa [prefixWord, tailWord_7539383, baseEnd_7539383] using wordTrace_append hprefix tailTrace_7539383
  have hstable : (prefixWord ++ tailWord_7539383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539383).length < 2 ^ (prefixWord ++ tailWord_7539383).sum := by decide
  have hdescent : baseEnd_7539383 < baseStart_7539383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539389 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 7]
def baseStart_7539389 : Nat := 118140960795 + 7539389 * 2 ^ 59
def prefixEnd_7539389 : Nat := 4983230072969 + 3 ^ 40 * 7539389 * 2
def baseEnd_7539389 : Nat := 430147822024523093284943

theorem tailTrace_7539389 : CollatzResearch.WordTrace tailWord_7539389 prefixEnd_7539389 430147822024523093284943 := by
  unfold tailWord_7539389
  simp only [CollatzResearch.WordTrace]
  refine ⟨274984107683088752973237221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183322738455392501982158147 274984107683088752973237221)
  ·
    refine ⟨51559520190579141182481979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274984107683088752973237221 51559520190579141182481979)
    ·
      refine ⟨77339280285868711773722969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51559520190579141182481979 77339280285868711773722969)
      ·
        refine ⟨58004460214401533830292227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77339280285868711773722969 58004460214401533830292227)
        ·
          refine ⟨87006690321602300745438341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58004460214401533830292227 87006690321602300745438341)
          ·
            refine ⟨16313754435300431389769689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87006690321602300745438341 16313754435300431389769689)
            ·
              refine ⟨12235315826475323542327267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16313754435300431389769689 12235315826475323542327267)
              ·
                refine ⟨18352973739712985313490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12235315826475323542327267 18352973739712985313490901)
                ·
                  refine ⟨430147822024523093284943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18352973739712985313490901 430147822024523093284943)
                  ·
                    rfl

theorem cell23_7539389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_7539389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539389 prefixEnd_7539389 := by exact prefixLift 7539389
  have htrace : WordTrace (prefixWord ++ tailWord_7539389) baseStart_7539389 baseEnd_7539389 := by
    simpa [prefixWord, tailWord_7539389, baseEnd_7539389] using wordTrace_append hprefix tailTrace_7539389
  have hstable : (prefixWord ++ tailWord_7539389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539389).length < 2 ^ (prefixWord ++ tailWord_7539389).sum := by decide
  have hdescent : baseEnd_7539389 < baseStart_7539389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539400 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_7539400 : Nat := 118140960795 + 7539400 * 2 ^ 59
def prefixEnd_7539400 : Nat := 4983230072969 + 3 ^ 40 * 7539400 * 2
def baseEnd_7539400 : Nat := 3871336046507907296526937

theorem tailTrace_7539400 : CollatzResearch.WordTrace tailWord_7539400 prefixEnd_7539400 3871336046507907296526937 := by
  unfold tailWord_7539400
  simp only [CollatzResearch.WordTrace]
  refine ⟨137492254443024450925943827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183323005924032601234591769 137492254443024450925943827)
  ·
    refine ⟨206238381664536676388915741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137492254443024450925943827 206238381664536676388915741)
    ·
      refine ⟨77339393124201253645843403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206238381664536676388915741 77339393124201253645843403)
      ·
        refine ⟨116009089686301880468765105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77339393124201253645843403 116009089686301880468765105)
        ·
          refine ⟨87006817264726410351573829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116009089686301880468765105 87006817264726410351573829)
          ·
            refine ⟨16313778237136201940920093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87006817264726410351573829 16313778237136201940920093)
            ·
              refine ⟨6117666838926075727845035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16313778237136201940920093 6117666838926075727845035)
              ·
                refine ⟨9176500258389113591767553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117666838926075727845035 9176500258389113591767553)
                ·
                  refine ⟨6882375193791835193825665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9176500258389113591767553 6882375193791835193825665)
                  ·
                    refine ⟨5161781395343876395369249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6882375193791835193825665 5161781395343876395369249)
                    ·
                      refine ⟨3871336046507907296526937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161781395343876395369249 3871336046507907296526937)
                      ·
                        rfl

theorem cell23_7539400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_7539400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539400 prefixEnd_7539400 := by exact prefixLift 7539400
  have htrace : WordTrace (prefixWord ++ tailWord_7539400) baseStart_7539400 baseEnd_7539400 := by
    simpa [prefixWord, tailWord_7539400, baseEnd_7539400] using wordTrace_append hprefix tailTrace_7539400
  have hstable : (prefixWord ++ tailWord_7539400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539400).length < 2 ^ (prefixWord ++ tailWord_7539400).sum := by decide
  have hdescent : baseEnd_7539400 < baseStart_7539400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539439 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_7539439 : Nat := 118140960795 + 7539439 * 2 ^ 59
def prefixEnd_7539439 : Nat := 4983230072969 + 3 ^ 40 * 7539439 * 2
def baseEnd_7539439 : Nat := 3871356072253432643939257

theorem tailTrace_7539439 : CollatzResearch.WordTrace tailWord_7539439 prefixEnd_7539439 3871356072253432643939257 := by
  unfold tailWord_7539439
  simp only [CollatzResearch.WordTrace]
  refine ⟨274985931332907611512557371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183323954221938407675038247 274985931332907611512557371)
  ·
    refine ⟨412478896999361417268836057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274985931332907611512557371 412478896999361417268836057)
    ·
      refine ⟨309359172749521062951627043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412478896999361417268836057 309359172749521062951627043)
      ·
        refine ⟨464038759124281594427440565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309359172749521062951627043 464038759124281594427440565)
        ·
          refine ⟨43503633667901399477572553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464038759124281594427440565 43503633667901399477572553)
          ·
            refine ⟨32627725250926049608179415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43503633667901399477572553 32627725250926049608179415)
            ·
              refine ⟨48941587876389074412269123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32627725250926049608179415 48941587876389074412269123)
              ·
                refine ⟨73412381814583611618403685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48941587876389074412269123 73412381814583611618403685)
                ·
                  refine ⟨13764821590234427178450691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73412381814583611618403685 13764821590234427178450691)
                  ·
                    refine ⟨20647232385351640767676037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13764821590234427178450691 20647232385351640767676037)
                    ·
                      refine ⟨3871356072253432643939257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20647232385351640767676037 3871356072253432643939257)
                      ·
                        rfl

theorem cell23_7539439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_7539439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539439 prefixEnd_7539439 := by exact prefixLift 7539439
  have htrace : WordTrace (prefixWord ++ tailWord_7539439) baseStart_7539439 baseEnd_7539439 := by
    simpa [prefixWord, tailWord_7539439, baseEnd_7539439] using wordTrace_append hprefix tailTrace_7539439
  have hstable : (prefixWord ++ tailWord_7539439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539439).length < 2 ^ (prefixWord ++ tailWord_7539439).sum := by decide
  have hdescent : baseEnd_7539439 < baseStart_7539439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539459 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3]
def baseStart_7539459 : Nat := 118140960795 + 7539459 * 2 ^ 59
def prefixEnd_7539459 : Nat := 4983230072969 + 3 ^ 40 * 7539459 * 2
def baseEnd_7539459 : Nat := 3871366341866522565689165

theorem tailTrace_7539459 : CollatzResearch.WordTrace tailWord_7539459 prefixEnd_7539459 3871366341866522565689165 := by
  unfold tailWord_7539459
  simp only [CollatzResearch.WordTrace]
  refine ⟨274986660792835154928285431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183324440528556769952190287 274986660792835154928285431)
  ·
    refine ⟨412479991189252732392428147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274986660792835154928285431 412479991189252732392428147)
    ·
      refine ⟨618719986783879098588642221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412479991189252732392428147 618719986783879098588642221)
      ·
        refine ⟨232019995043954661970740833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618719986783879098588642221 232019995043954661970740833)
        ·
          refine ⟨174014996282965996478055625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232019995043954661970740833 174014996282965996478055625)
          ·
            refine ⟨130511247212224497358541719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174014996282965996478055625 130511247212224497358541719)
            ·
              refine ⟨195766870818336746037812579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130511247212224497358541719 195766870818336746037812579)
              ·
                refine ⟨293650306227505119056718869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195766870818336746037812579 293650306227505119056718869)
                ·
                  refine ⟨13764858104414302455783697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293650306227505119056718869 13764858104414302455783697)
                  ·
                    refine ⟨10323643578310726841837773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13764858104414302455783697 10323643578310726841837773)
                    ·
                      refine ⟨3871366341866522565689165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323643578310726841837773 3871366341866522565689165)
                      ·
                        rfl

theorem cell23_7539459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_7539459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539459 prefixEnd_7539459 := by exact prefixLift 7539459
  have htrace : WordTrace (prefixWord ++ tailWord_7539459) baseStart_7539459 baseEnd_7539459 := by
    simpa [prefixWord, tailWord_7539459, baseEnd_7539459] using wordTrace_append hprefix tailTrace_7539459
  have hstable : (prefixWord ++ tailWord_7539459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539459).length < 2 ^ (prefixWord ++ tailWord_7539459).sum := by decide
  have hdescent : baseEnd_7539459 < baseStart_7539459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539496 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 6]
def baseStart_7539496 : Nat := 118140960795 + 7539496 * 2 ^ 59
def prefixEnd_7539496 : Nat := 4983230072969 + 3 ^ 40 * 7539496 * 2
def baseEnd_7539496 : Nat := 430153926738970991214055

theorem tailTrace_7539496 : CollatzResearch.WordTrace tailWord_7539496 prefixEnd_7539496 430153926738970991214055 := by
  unfold tailWord_7539496
  simp only [CollatzResearch.WordTrace]
  refine ⟨137494005146850555123691171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183325340195800740164921561 137494005146850555123691171)
  ·
    refine ⟨206241007720275832685536757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137494005146850555123691171 206241007720275832685536757)
    ·
      refine ⟨19335094473775859314269071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206241007720275832685536757 19335094473775859314269071)
      ·
        refine ⟨29002641710663788971403607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19335094473775859314269071 29002641710663788971403607)
        ·
          refine ⟨43503962565995683457105411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29002641710663788971403607 43503962565995683457105411)
          ·
            refine ⟨65255943848993525185658117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43503962565995683457105411 65255943848993525185658117)
            ·
              refine ⟨12235489471686285972310897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65255943848993525185658117 12235489471686285972310897)
              ·
                refine ⟨9176617103764714479233173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12235489471686285972310897 9176617103764714479233173)
                ·
                  refine ⟨430153926738970991214055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9176617103764714479233173 430153926738970991214055)
                  ·
                    rfl

theorem cell23_7539496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_7539496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539496 prefixEnd_7539496 := by exact prefixLift 7539496
  have htrace : WordTrace (prefixWord ++ tailWord_7539496) baseStart_7539496 baseEnd_7539496 := by
    simpa [prefixWord, tailWord_7539496, baseEnd_7539496] using wordTrace_append hprefix tailTrace_7539496
  have hstable : (prefixWord ++ tailWord_7539496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539496).length < 2 ^ (prefixWord ++ tailWord_7539496).sum := by decide
  have hdescent : baseEnd_7539496 < baseStart_7539496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539516 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 5, 2]
def baseStart_7539516 : Nat := 118140960795 + 7539516 * 2 ^ 59
def prefixEnd_7539516 : Nat := 4983230072969 + 3 ^ 40 * 7539516 * 2
def baseEnd_7539516 : Nat := 3871395610263828842676403

theorem tailTrace_7539516 : CollatzResearch.WordTrace tailWord_7539516 prefixEnd_7539516 3871395610263828842676403 := by
  unfold tailWord_7539516
  simp only [CollatzResearch.WordTrace]
  refine ⟨137494369876814326831555201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183325826502419102442073601 137494369876814326831555201)
  ·
    refine ⟨103120777407610745123666401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137494369876814326831555201 103120777407610745123666401)
    ·
      refine ⟨77340583055708058842749801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103120777407610745123666401 77340583055708058842749801)
      ·
        refine ⟨58005437291781044132062351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77340583055708058842749801 58005437291781044132062351)
        ·
          refine ⟨87008155937671566198093527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58005437291781044132062351 87008155937671566198093527)
          ·
            refine ⟨130512233906507349297140291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87008155937671566198093527 130512233906507349297140291)
            ·
              refine ⟨195768350859761023945710437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130512233906507349297140291 195768350859761023945710437)
              ·
                refine ⟨36706565786205191989820707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195768350859761023945710437 36706565786205191989820707)
                ·
                  refine ⟨55059848679307787984731061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36706565786205191989820707 55059848679307787984731061)
                  ·
                    refine ⟨5161860813685105123568537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55059848679307787984731061 5161860813685105123568537)
                    ·
                      refine ⟨3871395610263828842676403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161860813685105123568537 3871395610263828842676403)
                      ·
                        rfl

theorem cell23_7539516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_7539516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539516 prefixEnd_7539516 := by exact prefixLift 7539516
  have htrace : WordTrace (prefixWord ++ tailWord_7539516) baseStart_7539516 baseEnd_7539516 := by
    simpa [prefixWord, tailWord_7539516, baseEnd_7539516] using wordTrace_append hprefix tailTrace_7539516
  have hstable : (prefixWord ++ tailWord_7539516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539516).length < 2 ^ (prefixWord ++ tailWord_7539516).sum := by decide
  have hdescent : baseEnd_7539516 < baseStart_7539516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539543 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 1, 5]
def baseStart_7539543 : Nat := 118140960795 + 7539543 * 2 ^ 59
def prefixEnd_7539543 : Nat := 4983230072969 + 3 ^ 40 * 7539543 * 2
def baseEnd_7539543 : Nat := 1290469824747166745679593

theorem tailTrace_7539543 : CollatzResearch.WordTrace tailWord_7539543 prefixEnd_7539543 1290469824747166745679593 := by
  unfold tailWord_7539543
  simp only [CollatzResearch.WordTrace]
  refine ⟨274989724524530837274343283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183326483016353891516228855 274989724524530837274343283)
  ·
    refine ⟨412484586786796255911514925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274989724524530837274343283 412484586786796255911514925)
    ·
      refine ⟨154681720045048595966818097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412484586786796255911514925 154681720045048595966818097)
      ·
        refine ⟨116011290033786446975113573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154681720045048595966818097 116011290033786446975113573)
        ·
          refine ⟨21752116881334958807833795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116011290033786446975113573 21752116881334958807833795)
          ·
            refine ⟨32628175322002438211750693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21752116881334958807833795 32628175322002438211750693)
            ·
              refine ⟨6117782872875457164703255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32628175322002438211750693 6117782872875457164703255)
              ·
                refine ⟨9176674309313185747054883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117782872875457164703255 9176674309313185747054883)
                ·
                  refine ⟨13765011463969778620582325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9176674309313185747054883 13765011463969778620582325)
                  ·
                    refine ⟨1290469824747166745679593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13765011463969778620582325 1290469824747166745679593)
                    ·
                      rfl

theorem cell23_7539543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_7539543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539543 prefixEnd_7539543 := by exact prefixLift 7539543
  have htrace : WordTrace (prefixWord ++ tailWord_7539543) baseStart_7539543 baseEnd_7539543 := by
    simpa [prefixWord, tailWord_7539543, baseEnd_7539543] using wordTrace_append hprefix tailTrace_7539543
  have hstable : (prefixWord ++ tailWord_7539543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539543).length < 2 ^ (prefixWord ++ tailWord_7539543).sum := by decide
  have hdescent : baseEnd_7539543 < baseStart_7539543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539563 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 3, 2, 2]
def baseStart_7539563 : Nat := 118140960795 + 7539563 * 2 ^ 59
def prefixEnd_7539563 : Nat := 4983230072969 + 3 ^ 40 * 7539563 * 2
def baseEnd_7539563 : Nat := 3871419743854590158788687

theorem tailTrace_7539563 : CollatzResearch.WordTrace tailWord_7539563 prefixEnd_7539563 3871419743854590158788687 := by
  unfold tailWord_7539563
  simp only [CollatzResearch.WordTrace]
  refine ⟨274990453984458380690071343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183326969322972253793380895 274990453984458380690071343)
  ·
    refine ⟨412485680976687571035107015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274990453984458380690071343 412485680976687571035107015)
    ·
      refine ⟨618728521465031356552660523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412485680976687571035107015 618728521465031356552660523)
      ·
        refine ⟨928092782197547034828990785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618728521465031356552660523 928092782197547034828990785)
        ·
          refine ⟨696069586648160276121743089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928092782197547034828990785 696069586648160276121743089)
          ·
            refine ⟨522052189986120207091307317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696069586648160276121743089 522052189986120207091307317)
            ·
              refine ⟨48942392811198769414810061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522052189986120207091307317 48942392811198769414810061)
              ·
                refine ⟨18353397304199538530553773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48942392811198769414810061 18353397304199538530553773)
                ·
                  refine ⟨6882523989074826948957665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18353397304199538530553773 6882523989074826948957665)
                  ·
                    refine ⟨5161892991806120211718249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6882523989074826948957665 5161892991806120211718249)
                    ·
                      refine ⟨3871419743854590158788687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161892991806120211718249 3871419743854590158788687)
                      ·
                        rfl

theorem cell23_7539563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2, 2].length) (baseStart_7539563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539563 prefixEnd_7539563 := by exact prefixLift 7539563
  have htrace : WordTrace (prefixWord ++ tailWord_7539563) baseStart_7539563 baseEnd_7539563 := by
    simpa [prefixWord, tailWord_7539563, baseEnd_7539563] using wordTrace_append hprefix tailTrace_7539563
  have hstable : (prefixWord ++ tailWord_7539563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539563).length < 2 ^ (prefixWord ++ tailWord_7539563).sum := by decide
  have hdescent : baseEnd_7539563 < baseStart_7539563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539573 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7539573 : Nat := 118140960795 + 7539573 * 2 ^ 59
def prefixEnd_7539573 : Nat := 4983230072969 + 3 ^ 40 * 7539573 * 2
def baseEnd_7539573 : Nat := 1290474959553711706554547

theorem tailTrace_7539573 : CollatzResearch.WordTrace tailWord_7539573 prefixEnd_7539573 1290474959553711706554547 := by
  unfold tailWord_7539573
  simp only [CollatzResearch.WordTrace]
  refine ⟨274990818714422152397935373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183327212476281434931956915 274990818714422152397935373)
  ·
    refine ⟨103121557017908307149225765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274990818714422152397935373 103121557017908307149225765)
    ·
      refine ⟨19335291940857807590479831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103121557017908307149225765 19335291940857807590479831)
      ·
        refine ⟨29002937911286711385719747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19335291940857807590479831 29002937911286711385719747)
        ·
          refine ⟨43504406866930067078579621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29002937911286711385719747 43504406866930067078579621)
          ·
            refine ⟨8157076287549387577233679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43504406866930067078579621 8157076287549387577233679)
            ·
              refine ⟨12235614431324081365850519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157076287549387577233679 12235614431324081365850519)
              ·
                refine ⟨18353421646986122048775779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12235614431324081365850519 18353421646986122048775779)
                ·
                  refine ⟨27530132470479183073163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18353421646986122048775779 27530132470479183073163669)
                  ·
                    refine ⟨1290474959553711706554547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27530132470479183073163669 1290474959553711706554547)
                    ·
                      rfl

theorem cell23_7539573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7539573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539573 prefixEnd_7539573 := by exact prefixLift 7539573
  have htrace : WordTrace (prefixWord ++ tailWord_7539573) baseStart_7539573 baseEnd_7539573 := by
    simpa [prefixWord, tailWord_7539573, baseEnd_7539573] using wordTrace_append hprefix tailTrace_7539573
  have hstable : (prefixWord ++ tailWord_7539573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539573).length < 2 ^ (prefixWord ++ tailWord_7539573).sum := by decide
  have hdescent : baseEnd_7539573 < baseStart_7539573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539596 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 1, 3, 3]
def baseStart_7539596 : Nat := 118140960795 + 7539596 * 2 ^ 59
def prefixEnd_7539596 : Nat := 4983230072969 + 3 ^ 40 * 7539596 * 2
def baseEnd_7539596 : Nat := 3871436688716188529676035

theorem tailTrace_7539596 : CollatzResearch.WordTrace tailWord_7539596 prefixEnd_7539596 3871436688716188529676035 := by
  unfold tailWord_7539596
  simp only [CollatzResearch.WordTrace]
  refine ⟨137495828796669413663011321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183327771728892551550681761 137495828796669413663011321)
  ·
    refine ⟨103121871597502060247258491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137495828796669413663011321 103121871597502060247258491)
    ·
      refine ⟨154682807396253090370887737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103121871597502060247258491 154682807396253090370887737)
      ·
        refine ⟨116012105547189817778165803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154682807396253090370887737 116012105547189817778165803)
        ·
          refine ⟨174018158320784726667248705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116012105547189817778165803 174018158320784726667248705)
          ·
            refine ⟨130513618740588545000436529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174018158320784726667248705 130513618740588545000436529)
            ·
              refine ⟨97885214055441408750327397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130513618740588545000436529 97885214055441408750327397)
              ·
                refine ⟨18353477635395264140686387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97885214055441408750327397 18353477635395264140686387)
                ·
                  refine ⟨27530216453092896211029581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18353477635395264140686387 27530216453092896211029581)
                  ·
                    refine ⟨10323831169909836079136093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27530216453092896211029581 10323831169909836079136093)
                    ·
                      refine ⟨3871436688716188529676035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323831169909836079136093 3871436688716188529676035)
                      ·
                        rfl

theorem cell23_7539596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_7539596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539596 prefixEnd_7539596 := by exact prefixLift 7539596
  have htrace : WordTrace (prefixWord ++ tailWord_7539596) baseStart_7539596 baseEnd_7539596 := by
    simpa [prefixWord, tailWord_7539596, baseEnd_7539596] using wordTrace_append hprefix tailTrace_7539596
  have hstable : (prefixWord ++ tailWord_7539596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539596).length < 2 ^ (prefixWord ++ tailWord_7539596).sum := by decide
  have hdescent : baseEnd_7539596 < baseStart_7539596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539609 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_7539609 : Nat := 118140960795 + 7539609 * 2 ^ 59
def prefixEnd_7539609 : Nat := 4983230072969 + 3 ^ 40 * 7539609 * 2
def baseEnd_7539609 : Nat := 3871443363964696978813475

theorem tailTrace_7539609 : CollatzResearch.WordTrace tailWord_7539609 prefixEnd_7539609 3871443363964696978813475 := by
  unfold tailWord_7539609
  simp only [CollatzResearch.WordTrace]
  refine ⟨274992131742291730546245881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183328087828194487030830587 274992131742291730546245881)
  ·
    refine ⟨206244098806718797909684411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274992131742291730546245881 206244098806718797909684411)
    ·
      refine ⟨309366148210078196864526617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206244098806718797909684411 309366148210078196864526617)
      ·
        refine ⟨232024611157558647648394963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309366148210078196864526617 232024611157558647648394963)
        ·
          refine ⟨348036916736337971472592445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232024611157558647648394963 348036916736337971472592445)
          ·
            refine ⟨130513843776126739302222167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348036916736337971472592445 130513843776126739302222167)
            ·
              refine ⟨195770765664190108953333251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130513843776126739302222167 195770765664190108953333251)
              ·
                refine ⟨293656148496285163429999877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195770765664190108953333251 293656148496285163429999877)
                ·
                  refine ⟨55060527843053468143124977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293656148496285163429999877 55060527843053468143124977)
                  ·
                    refine ⟨41295395882290101107343733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55060527843053468143124977 41295395882290101107343733)
                    ·
                      refine ⟨3871443363964696978813475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41295395882290101107343733 3871443363964696978813475)
                      ·
                        rfl

theorem cell23_7539609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_7539609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539609 prefixEnd_7539609 := by exact prefixLift 7539609
  have htrace : WordTrace (prefixWord ++ tailWord_7539609) baseStart_7539609 baseEnd_7539609 := by
    simpa [prefixWord, tailWord_7539609, baseEnd_7539609] using wordTrace_append hprefix tailTrace_7539609
  have hstable : (prefixWord ++ tailWord_7539609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539609).length < 2 ^ (prefixWord ++ tailWord_7539609).sum := by decide
  have hdescent : baseEnd_7539609 < baseStart_7539609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539613 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_7539613 : Nat := 118140960795 + 7539613 * 2 ^ 59
def prefixEnd_7539613 : Nat := 4983230072969 + 3 ^ 40 * 7539613 * 2
def baseEnd_7539613 : Nat := 3871445417887314963163457

theorem tailTrace_7539613 : CollatzResearch.WordTrace tailWord_7539613 prefixEnd_7539613 3871445417887314963163457 := by
  unfold tailWord_7539613
  simp only [CollatzResearch.WordTrace]
  refine ⟨274992277634277239229391493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183328185089518159486260995 274992277634277239229391493)
  ·
    refine ⟨51561052056426982355510905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274992277634277239229391493 51561052056426982355510905)
    ·
      refine ⟨38670789042320236766633179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51561052056426982355510905 38670789042320236766633179)
      ·
        refine ⟨58006183563480355149949769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38670789042320236766633179 58006183563480355149949769)
        ·
          refine ⟨43504637672610266362462327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58006183563480355149949769 43504637672610266362462327)
          ·
            refine ⟨65256956508915399543693491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43504637672610266362462327 65256956508915399543693491)
            ·
              refine ⟨97885434763373099315540237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65256956508915399543693491 97885434763373099315540237)
              ·
                refine ⟨36707038036264912243327589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97885434763373099315540237 36707038036264912243327589)
                ·
                  refine ⟨6882569631799671045623923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36707038036264912243327589 6882569631799671045623923)
                  ·
                    refine ⟨10323854447699506568435885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882569631799671045623923 10323854447699506568435885)
                    ·
                      refine ⟨3871445417887314963163457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10323854447699506568435885 3871445417887314963163457)
                      ·
                        rfl

theorem cell23_7539613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_7539613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539613 prefixEnd_7539613 := by exact prefixLift 7539613
  have htrace : WordTrace (prefixWord ++ tailWord_7539613) baseStart_7539613 baseEnd_7539613 := by
    simpa [prefixWord, tailWord_7539613, baseEnd_7539613] using wordTrace_append hprefix tailTrace_7539613
  have hstable : (prefixWord ++ tailWord_7539613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539613).length < 2 ^ (prefixWord ++ tailWord_7539613).sum := by decide
  have hdescent : baseEnd_7539613 < baseStart_7539613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539640 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_7539640 : Nat := 118140960795 + 7539640 * 2 ^ 59
def prefixEnd_7539640 : Nat := 4983230072969 + 3 ^ 40 * 7539640 * 2
def baseEnd_7539640 : Nat := 3871459281864986357525833

theorem tailTrace_7539640 : CollatzResearch.WordTrace tailWord_7539640 prefixEnd_7539640 3871459281864986357525833 := by
  unfold tailWord_7539640
  simp only [CollatzResearch.WordTrace]
  refine ⟨137496631202589711420312187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183328841603452948560416249 137496631202589711420312187)
  ·
    refine ⟨206244946803884567130468281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137496631202589711420312187 206244946803884567130468281)
    ·
      refine ⟨154683710102913425347851211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206244946803884567130468281 154683710102913425347851211)
      ·
        refine ⟨232025565154370138021776817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154683710102913425347851211 232025565154370138021776817)
        ·
          refine ⟨174019173865777603516332613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232025565154370138021776817 174019173865777603516332613)
          ·
            refine ⟨32628595099833300659312365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174019173865777603516332613 32628595099833300659312365)
            ·
              refine ⟨12235723162437487747242137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32628595099833300659312365 12235723162437487747242137)
              ·
                refine ⟨9176792371828115810431603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12235723162437487747242137 9176792371828115810431603)
                ·
                  refine ⟨13765188557742173715647405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9176792371828115810431603 13765188557742173715647405)
                  ·
                    refine ⟨5161945709153315143367777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13765188557742173715647405 5161945709153315143367777)
                    ·
                      refine ⟨3871459281864986357525833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161945709153315143367777 3871459281864986357525833)
                      ·
                        rfl

theorem cell23_7539640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_7539640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539640 prefixEnd_7539640 := by exact prefixLift 7539640
  have htrace : WordTrace (prefixWord ++ tailWord_7539640) baseStart_7539640 baseEnd_7539640 := by
    simpa [prefixWord, tailWord_7539640, baseEnd_7539640] using wordTrace_append hprefix tailTrace_7539640
  have hstable : (prefixWord ++ tailWord_7539640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539640).length < 2 ^ (prefixWord ++ tailWord_7539640).sum := by decide
  have hdescent : baseEnd_7539640 < baseStart_7539640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539687 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7539687 : Nat := 118140960795 + 7539687 * 2 ^ 59
def prefixEnd_7539687 : Nat := 4983230072969 + 3 ^ 40 * 7539687 * 2
def baseEnd_7539687 : Nat := 3871483415455747673638117

theorem tailTrace_7539687 : CollatzResearch.WordTrace tailWord_7539687 prefixEnd_7539687 3871483415455747673638117 := by
  unfold tailWord_7539687
  simp only [CollatzResearch.WordTrace]
  refine ⟨274994976636009149867585315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183329984424006099911723543 274994976636009149867585315)
  ·
    refine ⟨412492464954013724801377973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274994976636009149867585315 412492464954013724801377973)
    ·
      refine ⟨38671168589438786700129185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 412492464954013724801377973 38671168589438786700129185)
      ·
        refine ⟨29003376442079090025096889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38671168589438786700129185 29003376442079090025096889)
        ·
          refine ⟨21752532331559317518822667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29003376442079090025096889 21752532331559317518822667)
          ·
            refine ⟨32628798497338976278234001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21752532331559317518822667 32628798497338976278234001)
            ·
              refine ⟨24471598873004232208675501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32628798497338976278234001 24471598873004232208675501)
              ·
                refine ⟨9176849577376587078253313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24471598873004232208675501 9176849577376587078253313)
                ·
                  refine ⟨6882637183032440308689985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9176849577376587078253313 6882637183032440308689985)
                  ·
                    refine ⟨5161977887274330231517489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6882637183032440308689985 5161977887274330231517489)
                    ·
                      refine ⟨3871483415455747673638117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5161977887274330231517489 3871483415455747673638117)
                      ·
                        rfl

theorem cell23_7539687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7539687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539687 prefixEnd_7539687 := by exact prefixLift 7539687
  have htrace : WordTrace (prefixWord ++ tailWord_7539687) baseStart_7539687 baseEnd_7539687 := by
    simpa [prefixWord, tailWord_7539687, baseEnd_7539687] using wordTrace_append hprefix tailTrace_7539687
  have hstable : (prefixWord ++ tailWord_7539687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539687).length < 2 ^ (prefixWord ++ tailWord_7539687).sum := by decide
  have hdescent : baseEnd_7539687 < baseStart_7539687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539756 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 4]
def baseStart_7539756 : Nat := 118140960795 + 7539756 * 2 ^ 59
def prefixEnd_7539756 : Nat := 4983230072969 + 3 ^ 40 * 7539756 * 2
def baseEnd_7539756 : Nat := 3871518845620907903675299

theorem tailTrace_7539756 : CollatzResearch.WordTrace tailWord_7539756 prefixEnd_7539756 3871518845620907903675299 := by
  unfold tailWord_7539756
  simp only [CollatzResearch.WordTrace]
  refine ⟨137498746636379587325923561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183331662181839449767898081 137498746636379587325923561)
  ·
    refine ⟨103124059977284690494442671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137498746636379587325923561 103124059977284690494442671)
    ·
      refine ⟨154686089965927035741664007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103124059977284690494442671 154686089965927035741664007)
      ·
        refine ⟨232029134948890553612496011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154686089965927035741664007 232029134948890553612496011)
        ·
          refine ⟨348043702423335830418744017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232029134948890553612496011 348043702423335830418744017)
          ·
            refine ⟨261032776817501872814058013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348043702423335830418744017 261032776817501872814058013)
            ·
              refine ⟨97887291306563202305271755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261032776817501872814058013 97887291306563202305271755)
              ·
                refine ⟨146830936959844803457907633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97887291306563202305271755 146830936959844803457907633)
                ·
                  refine ⟨110123202719883602593430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146830936959844803457907633 110123202719883602593430725)
                  ·
                    refine ⟨20648100509978175486268261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110123202719883602593430725 20648100509978175486268261)
                    ·
                      refine ⟨3871518845620907903675299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20648100509978175486268261 3871518845620907903675299)
                      ·
                        rfl

theorem cell23_7539756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_7539756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539756 prefixEnd_7539756 := by exact prefixLift 7539756
  have htrace : WordTrace (prefixWord ++ tailWord_7539756) baseStart_7539756 baseEnd_7539756 := by
    simpa [prefixWord, tailWord_7539756, baseEnd_7539756] using wordTrace_append hprefix tailTrace_7539756
  have hstable : (prefixWord ++ tailWord_7539756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539756).length < 2 ^ (prefixWord ++ tailWord_7539756).sum := by decide
  have hdescent : baseEnd_7539756 < baseStart_7539756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539763 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3]
def baseStart_7539763 : Nat := 118140960795 + 7539763 * 2 ^ 59
def prefixEnd_7539763 : Nat := 4983230072969 + 3 ^ 40 * 7539763 * 2
def baseEnd_7539763 : Nat := 3871522439985489376287767

theorem tailTrace_7539763 : CollatzResearch.WordTrace tailWord_7539763 prefixEnd_7539763 3871522439985489376287767 := by
  unfold tailWord_7539763
  simp only [CollatzResearch.WordTrace]
  refine ⟨274997748583733814847351943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183331832389155876564901295 274997748583733814847351943)
  ·
    refine ⟨412496622875600722271027915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274997748583733814847351943 412496622875600722271027915)
    ·
      refine ⟨618744934313401083406541873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412496622875600722271027915 618744934313401083406541873)
      ·
        refine ⟨464058700735050812554906405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618744934313401083406541873 464058700735050812554906405)
        ·
          refine ⟨87011006387822027354044951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464058700735050812554906405 87011006387822027354044951)
          ·
            refine ⟨130516509581733041031067427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87011006387822027354044951 130516509581733041031067427)
            ·
              refine ⟨195774764372599561546601141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130516509581733041031067427 195774764372599561546601141)
              ·
                refine ⟨18353884159931208894993857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195774764372599561546601141 18353884159931208894993857)
                ·
                  refine ⟨13765413119948406671245393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18353884159931208894993857 13765413119948406671245393)
                  ·
                    refine ⟨10324059839961305003434045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13765413119948406671245393 10324059839961305003434045)
                    ·
                      refine ⟨3871522439985489376287767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324059839961305003434045 3871522439985489376287767)
                      ·
                        rfl

theorem cell23_7539763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_7539763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539763 prefixEnd_7539763 := by exact prefixLift 7539763
  have htrace : WordTrace (prefixWord ++ tailWord_7539763) baseStart_7539763 baseEnd_7539763 := by
    simpa [prefixWord, tailWord_7539763, baseEnd_7539763] using wordTrace_append hprefix tailTrace_7539763
  have hstable : (prefixWord ++ tailWord_7539763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539763).length < 2 ^ (prefixWord ++ tailWord_7539763).sum := by decide
  have hdescent : baseEnd_7539763 < baseStart_7539763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539786 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_7539786 : Nat := 118140960795 + 7539786 * 2 ^ 59
def prefixEnd_7539786 : Nat := 4983230072969 + 3 ^ 40 * 7539786 * 2
def baseEnd_7539786 : Nat := 3871534250040542786300161

theorem tailTrace_7539786 : CollatzResearch.WordTrace tailWord_7539786 prefixEnd_7539786 3871534250040542786300161 := by
  unfold tailWord_7539786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68749646865662622443859803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183332391641766993183626141 68749646865662622443859803)
  ·
    refine ⟨103124470298493933665789705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68749646865662622443859803 103124470298493933665789705)
    ·
      refine ⟨77343352723870450249342279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103124470298493933665789705 77343352723870450249342279)
      ·
        refine ⟨116015029085805675374013419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77343352723870450249342279 116015029085805675374013419)
        ·
          refine ⟨174022543628708513061020129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116015029085805675374013419 174022543628708513061020129)
          ·
            refine ⟨130516907721531384795765097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174022543628708513061020129 130516907721531384795765097)
            ·
              refine ⟨97887680791148538596823823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130516907721531384795765097 97887680791148538596823823)
              ·
                refine ⟨146831521186722807895235735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97887680791148538596823823 146831521186722807895235735)
                ·
                  refine ⟨220247281780084211842853603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146831521186722807895235735 220247281780084211842853603)
                  ·
                    refine ⟨330370922670126317764280405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220247281780084211842853603 330370922670126317764280405)
                    ·
                      refine ⟨3871534250040542786300161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 330370922670126317764280405 3871534250040542786300161)
                      ·
                        rfl

theorem cell23_7539786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_7539786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539786 prefixEnd_7539786 := by exact prefixLift 7539786
  have htrace : WordTrace (prefixWord ++ tailWord_7539786) baseStart_7539786 baseEnd_7539786 := by
    simpa [prefixWord, tailWord_7539786, baseEnd_7539786] using wordTrace_append hprefix tailTrace_7539786
  have hstable : (prefixWord ++ tailWord_7539786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539786).length < 2 ^ (prefixWord ++ tailWord_7539786).sum := by decide
  have hdescent : baseEnd_7539786 < baseStart_7539786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539813 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_7539813 : Nat := 118140960795 + 7539813 * 2 ^ 59
def prefixEnd_7539813 : Nat := 4983230072969 + 3 ^ 40 * 7539813 * 2
def baseEnd_7539813 : Nat := 1290516038006071393554179

theorem tailTrace_7539813 : CollatzResearch.WordTrace tailWord_7539813 prefixEnd_7539813 1290516038006071393554179 := by
  unfold tailWord_7539813
  simp only [CollatzResearch.WordTrace]
  refine ⟨274999572233552673386672093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183333048155701782257781395 274999572233552673386672093)
  ·
    refine ⟨103124839587582252520002035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274999572233552673386672093 103124839587582252520002035)
    ·
      refine ⟨154687259381373378780003053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103124839587582252520002035 154687259381373378780003053)
      ·
        refine ⟨58007722268015017042501145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154687259381373378780003053 58007722268015017042501145)
        ·
          refine ⟨43505791701011262781875859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58007722268015017042501145 43505791701011262781875859)
          ·
            refine ⟨65258687551516894172813789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43505791701011262781875859 65258687551516894172813789)
            ·
              refine ⟨24472007831818835314805171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65258687551516894172813789 24472007831818835314805171)
              ·
                refine ⟨36708011747728252972207757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24472007831818835314805171 36708011747728252972207757)
                ·
                  refine ⟨13765504405398094864577909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36708011747728252972207757 13765504405398094864577909)
                  ·
                    refine ⟨1290516038006071393554179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13765504405398094864577909 1290516038006071393554179)
                    ·
                      rfl

theorem cell23_7539813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_7539813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539813 prefixEnd_7539813 := by exact prefixLift 7539813
  have htrace : WordTrace (prefixWord ++ tailWord_7539813) baseStart_7539813 baseEnd_7539813 := by
    simpa [prefixWord, tailWord_7539813, baseEnd_7539813] using wordTrace_append hprefix tailTrace_7539813
  have hstable : (prefixWord ++ tailWord_7539813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539813).length < 2 ^ (prefixWord ++ tailWord_7539813).sum := by decide
  have hdescent : baseEnd_7539813 < baseStart_7539813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539838 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_7539838 : Nat := 118140960795 + 7539838 * 2 ^ 59
def prefixEnd_7539838 : Nat := 4983230072969 + 3 ^ 40 * 7539838 * 2
def baseEnd_7539838 : Nat := 1290520317011525527616641

theorem tailTrace_7539838 : CollatzResearch.WordTrace tailWord_7539838 prefixEnd_7539838 1290520317011525527616641 := by
  unfold tailWord_7539838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34375060507307762832041521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183333656038974735104221445 34375060507307762832041521)
  ·
    refine ⟨25781295380480822124031141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34375060507307762832041521 25781295380480822124031141)
    ·
      refine ⟨4833992883840154148255839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25781295380480822124031141 4833992883840154148255839)
      ·
        refine ⟨7250989325760231222383759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833992883840154148255839 7250989325760231222383759)
        ·
          refine ⟨10876483988640346833575639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250989325760231222383759 10876483988640346833575639)
          ·
            refine ⟨16314725982960520250363459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10876483988640346833575639 16314725982960520250363459)
            ·
              refine ⟨24472088974440780375545189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16314725982960520250363459 24472088974440780375545189)
              ·
                refine ⟨4588516682707646320414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24472088974440780375545189 4588516682707646320414723)
                ·
                  refine ⟨6882775024061469480622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588516682707646320414723 6882775024061469480622085)
                  ·
                    refine ⟨1290520317011525527616641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882775024061469480622085 1290520317011525527616641)
                    ·
                      rfl

theorem cell23_7539838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_7539838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539838 prefixEnd_7539838 := by exact prefixLift 7539838
  have htrace : WordTrace (prefixWord ++ tailWord_7539838) baseStart_7539838 baseEnd_7539838 := by
    simpa [prefixWord, tailWord_7539838, baseEnd_7539838] using wordTrace_append hprefix tailTrace_7539838
  have hstable : (prefixWord ++ tailWord_7539838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539838).length < 2 ^ (prefixWord ++ tailWord_7539838).sum := by decide
  have hdescent : baseEnd_7539838 < baseStart_7539838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539844 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_7539844 : Nat := 118140960795 + 7539844 * 2 ^ 59
def prefixEnd_7539844 : Nat := 4983230072969 + 3 ^ 40 * 7539844 * 2
def baseEnd_7539844 : Nat := 3871564031918503559374895

theorem tailTrace_7539844 : CollatzResearch.WordTrace tailWord_7539844 prefixEnd_7539844 3871564031918503559374895 := by
  unfold tailWord_7539844
  simp only [CollatzResearch.WordTrace]
  refine ⟨137500351448220182840525293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183333801930960243787367057 137500351448220182840525293)
  ·
    refine ⟨51562631793082568565196985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137500351448220182840525293 51562631793082568565196985)
    ·
      refine ⟨38671973844811926423897739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51562631793082568565196985 38671973844811926423897739)
      ·
        refine ⟨58007960767217889635846609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38671973844811926423897739 58007960767217889635846609)
        ·
          refine ⟨43505970575413417226884957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58007960767217889635846609 43505970575413417226884957)
          ·
            refine ⟨16314738965780031460081859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43505970575413417226884957 16314738965780031460081859)
            ·
              refine ⟨24472108448670047190122789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16314738965780031460081859 24472108448670047190122789)
              ·
                refine ⟨4588520334125633848148023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24472108448670047190122789 4588520334125633848148023)
                ·
                  refine ⟨6882780501188450772222035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588520334125633848148023 6882780501188450772222035)
                  ·
                    refine ⟨10324170751782676158333053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6882780501188450772222035 10324170751782676158333053)
                    ·
                      refine ⟨3871564031918503559374895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324170751782676158333053 3871564031918503559374895)
                      ·
                        rfl

theorem cell23_7539844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_7539844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539844 prefixEnd_7539844 := by exact prefixLift 7539844
  have htrace : WordTrace (prefixWord ++ tailWord_7539844) baseStart_7539844 baseEnd_7539844 := by
    simpa [prefixWord, tailWord_7539844, baseEnd_7539844] using wordTrace_append hprefix tailTrace_7539844
  have hstable : (prefixWord ++ tailWord_7539844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539844).length < 2 ^ (prefixWord ++ tailWord_7539844).sum := by decide
  have hdescent : baseEnd_7539844 < baseStart_7539844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539856 : List Nat := [2, 1, 1, 1, 1, 1, 4, 12]
def baseStart_7539856 : Nat := 118140960795 + 7539856 * 2 ^ 59
def prefixEnd_7539856 : Nat := 4983230072969 + 3 ^ 40 * 7539856 * 2
def baseEnd_7539856 : Nat := 143391488655050278237957

theorem tailTrace_7539856 : CollatzResearch.WordTrace tailWord_7539856 prefixEnd_7539856 143391488655050278237957 := by
  unfold tailWord_7539856
  simp only [CollatzResearch.WordTrace]
  refine ⟨137500570286198445865243711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183334093714931261153658281 137500570286198445865243711)
  ·
    refine ⟨206250855429297668797865567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137500570286198445865243711 206250855429297668797865567)
    ·
      refine ⟨309376283143946503196798351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206250855429297668797865567 309376283143946503196798351)
      ·
        refine ⟨464064424715919754795197527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309376283143946503196798351 464064424715919754795197527)
        ·
          refine ⟨696096637073879632192796291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464064424715919754795197527 696096637073879632192796291)
          ·
            refine ⟨1044144955610819448289194437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696096637073879632192796291 1044144955610819448289194437)
            ·
              refine ⟨195777179177028646554223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1044144955610819448289194437 195777179177028646554223957)
              ·
                refine ⟨143391488655050278237957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 195777179177028646554223957 143391488655050278237957)
                ·
                  rfl

theorem cell23_7539856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 12].length) (baseStart_7539856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539856 prefixEnd_7539856 := by exact prefixLift 7539856
  have htrace : WordTrace (prefixWord ++ tailWord_7539856) baseStart_7539856 baseEnd_7539856 := by
    simpa [prefixWord, tailWord_7539856, baseEnd_7539856] using wordTrace_append hprefix tailTrace_7539856
  have hstable : (prefixWord ++ tailWord_7539856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539856).length < 2 ^ (prefixWord ++ tailWord_7539856).sum := by decide
  have hdescent : baseEnd_7539856 < baseStart_7539856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539871 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7539871 : Nat := 118140960795 + 7539871 * 2 ^ 59
def prefixEnd_7539871 : Nat := 4983230072969 + 3 ^ 40 * 7539871 * 2
def baseEnd_7539871 : Nat := 3871577895896174953737271

theorem tailTrace_7539871 : CollatzResearch.WordTrace tailWord_7539871 prefixEnd_7539871 3871577895896174953737271 := by
  unfold tailWord_7539871
  simp only [CollatzResearch.WordTrace]
  refine ⟨275001687667342549292283467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183334458444895032861522311 275001687667342549292283467)
  ·
    refine ⟨412502531501013823938425201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275001687667342549292283467 412502531501013823938425201)
    ·
      refine ⟨309376898625760367953818901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412502531501013823938425201 309376898625760367953818901)
      ·
        refine ⟨14502042123082517247835261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309376898625760367953818901 14502042123082517247835261)
        ·
          refine ⟨5438265796155943967938223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14502042123082517247835261 5438265796155943967938223)
          ·
            refine ⟨8157398694233915951907335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438265796155943967938223 8157398694233915951907335)
            ·
              refine ⟨12236098041350873927861003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157398694233915951907335 12236098041350873927861003)
              ·
                refine ⟨18354147062026310891791505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12236098041350873927861003 18354147062026310891791505)
                ·
                  refine ⟨13765610296519733168843629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18354147062026310891791505 13765610296519733168843629)
                  ·
                    refine ⟨5162103861194899938316361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13765610296519733168843629 5162103861194899938316361)
                    ·
                      refine ⟨3871577895896174953737271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162103861194899938316361 3871577895896174953737271)
                      ·
                        rfl

theorem cell23_7539871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7539871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539871 prefixEnd_7539871 := by exact prefixLift 7539871
  have htrace : WordTrace (prefixWord ++ tailWord_7539871) baseStart_7539871 baseEnd_7539871 := by
    simpa [prefixWord, tailWord_7539871, baseEnd_7539871] using wordTrace_append hprefix tailTrace_7539871
  have hstable : (prefixWord ++ tailWord_7539871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539871).length < 2 ^ (prefixWord ++ tailWord_7539871).sum := by decide
  have hdescent : baseEnd_7539871 < baseStart_7539871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539887 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 1, 2, 3]
def baseStart_7539887 : Nat := 118140960795 + 7539887 * 2 ^ 59
def prefixEnd_7539887 : Nat := 4983230072969 + 3 ^ 40 * 7539887 * 2
def baseEnd_7539887 : Nat := 3871586111586646891137197

theorem tailTrace_7539887 : CollatzResearch.WordTrace tailWord_7539887 prefixEnd_7539887 3871586111586646891137197 := by
  unfold tailWord_7539887
  simp only [CollatzResearch.WordTrace]
  refine ⟨275002271235284584024865915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183334847490189722683243943 275002271235284584024865915)
  ·
    refine ⟨412503406852926876037298873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275002271235284584024865915 412503406852926876037298873)
    ·
      refine ⟨309377555139695157027974155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412503406852926876037298873 309377555139695157027974155)
      ·
        refine ⟨464066332709542735541961233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309377555139695157027974155 464066332709542735541961233)
        ·
          refine ⟨348049749532157051656470925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464066332709542735541961233 348049749532157051656470925)
          ·
            refine ⟨130518656074558894371176597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348049749532157051656470925 130518656074558894371176597)
            ·
              refine ⟨6118062003494948173648903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130518656074558894371176597 6118062003494948173648903)
              ·
                refine ⟨9177093005242422260473355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118062003494948173648903 9177093005242422260473355)
                ·
                  refine ⟨13765639507863633390710033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177093005242422260473355 13765639507863633390710033)
                  ·
                    refine ⟨10324229630897725043032525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13765639507863633390710033 10324229630897725043032525)
                    ·
                      refine ⟨3871586111586646891137197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324229630897725043032525 3871586111586646891137197)
                      ·
                        rfl

theorem cell23_7539887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 2, 3].length) (baseStart_7539887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539887 prefixEnd_7539887 := by exact prefixLift 7539887
  have htrace : WordTrace (prefixWord ++ tailWord_7539887) baseStart_7539887 baseEnd_7539887 := by
    simpa [prefixWord, tailWord_7539887, baseEnd_7539887] using wordTrace_append hprefix tailTrace_7539887
  have hstable : (prefixWord ++ tailWord_7539887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539887).length < 2 ^ (prefixWord ++ tailWord_7539887).sum := by decide
  have hdescent : baseEnd_7539887 < baseStart_7539887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539924 : List Nat := [2, 4, 1, 4, 1, 2, 2, 7]
def baseStart_7539924 : Nat := 118140960795 + 7539924 * 2 ^ 59
def prefixEnd_7539924 : Nat := 4983230072969 + 3 ^ 40 * 7539924 * 2
def baseEnd_7539924 : Nat := 143392781865587527643501

theorem tailTrace_7539924 : CollatzResearch.WordTrace tailWord_7539924 prefixEnd_7539924 143392781865587527643501 := by
  unfold tailWord_7539924
  simp only [CollatzResearch.WordTrace]
  refine ⟨137501810368075269671981413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183335747157433692895975217 137501810368075269671981413)
  ·
    refine ⟨25781589444014113063496515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137501810368075269671981413 25781589444014113063496515)
    ·
      refine ⟨38672384166021169595244773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25781589444014113063496515 38672384166021169595244773)
      ·
        refine ⟨7251072031128969299108395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38672384166021169595244773 7251072031128969299108395)
        ·
          refine ⟨10876608046693453948662593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251072031128969299108395 10876608046693453948662593)
          ·
            refine ⟨8157456035020090461496945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10876608046693453948662593 8157456035020090461496945)
            ·
              refine ⟨6118092026265067846122709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157456035020090461496945 6118092026265067846122709)
              ·
                refine ⟨143392781865587527643501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6118092026265067846122709 143392781865587527643501)
                ·
                  rfl

theorem cell23_7539924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 7].length) (baseStart_7539924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539924 prefixEnd_7539924 := by exact prefixLift 7539924
  have htrace : WordTrace (prefixWord ++ tailWord_7539924) baseStart_7539924 baseEnd_7539924 := by
    simpa [prefixWord, tailWord_7539924, baseEnd_7539924] using wordTrace_append hprefix tailTrace_7539924
  have hstable : (prefixWord ++ tailWord_7539924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539924).length < 2 ^ (prefixWord ++ tailWord_7539924).sum := by decide
  have hdescent : baseEnd_7539924 < baseStart_7539924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7539927 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_7539927 : Nat := 118140960795 + 7539927 * 2 ^ 59
def prefixEnd_7539927 : Nat := 4983230072969 + 3 ^ 40 * 7539927 * 2
def baseEnd_7539927 : Nat := 3871606650812826734637013

theorem tailTrace_7539927 : CollatzResearch.WordTrace tailWord_7539927 prefixEnd_7539927 3871606650812826734637013 := by
  unfold tailWord_7539927
  simp only [CollatzResearch.WordTrace]
  refine ⟨275003730155139670856322035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183335820103426447237548023 275003730155139670856322035)
  ·
    refine ⟨412505595232709506284483053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275003730155139670856322035 412505595232709506284483053)
    ·
      refine ⟨154689598212266064856681145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412505595232709506284483053 154689598212266064856681145)
      ·
        refine ⟨116017198659199548642510859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154689598212266064856681145 116017198659199548642510859)
        ·
          refine ⟨174025797988799322963766289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116017198659199548642510859 174025797988799322963766289)
          ·
            refine ⟨130519348491599492222824717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174025797988799322963766289 130519348491599492222824717)
            ·
              refine ⟨48944755684349809583559269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130519348491599492222824717 48944755684349809583559269)
              ·
                refine ⟨9177141690815589296917363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48944755684349809583559269 9177141690815589296917363)
                ·
                  refine ⟨13765712536223383945376045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177141690815589296917363 13765712536223383945376045)
                  ·
                    refine ⟨5162142201083768979516017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13765712536223383945376045 5162142201083768979516017)
                    ·
                      refine ⟨3871606650812826734637013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162142201083768979516017 3871606650812826734637013)
                      ·
                        rfl

theorem cell23_7539927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_7539927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7539927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7539927 prefixEnd_7539927 := by exact prefixLift 7539927
  have htrace : WordTrace (prefixWord ++ tailWord_7539927) baseStart_7539927 baseEnd_7539927 := by
    simpa [prefixWord, tailWord_7539927, baseEnd_7539927] using wordTrace_append hprefix tailTrace_7539927
  have hstable : (prefixWord ++ tailWord_7539927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7539927).length < 2 ^ (prefixWord ++ tailWord_7539927).sum := by decide
  have hdescent : baseEnd_7539927 < baseStart_7539927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7539927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540017 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_7540017 : Nat := 118140960795 + 7540017 * 2 ^ 59
def prefixEnd_7540017 : Nat := 4983230072969 + 3 ^ 40 * 7540017 * 2
def baseEnd_7540017 : Nat := 3871652864071731382511599

theorem tailTrace_7540017 : CollatzResearch.WordTrace tailWord_7540017 prefixEnd_7540017 3871652864071731382511599 := by
  unfold tailWord_7540017
  simp only [CollatzResearch.WordTrace]
  refine ⟨275007012724813616227098305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183338008483209077484732203 275007012724813616227098305)
  ·
    refine ⟨206255259543610212170323729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275007012724813616227098305 206255259543610212170323729)
    ·
      refine ⟨154691444657707659127742797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206255259543610212170323729 154691444657707659127742797)
      ·
        refine ⟨58009291746640372172903549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154691444657707659127742797 58009291746640372172903549)
        ·
          refine ⟨21753484404990139564838831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58009291746640372172903549 21753484404990139564838831)
          ·
            refine ⟨32630226607485209347258247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21753484404990139564838831 32630226607485209347258247)
            ·
              refine ⟨48945339911227814020887371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32630226607485209347258247 48945339911227814020887371)
              ·
                refine ⟨73418009866841721031331057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48945339911227814020887371 73418009866841721031331057)
                ·
                  refine ⟨55063507400131290773498293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73418009866841721031331057 55063507400131290773498293)
                  ·
                    refine ⟨5162203818762308510015465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55063507400131290773498293 5162203818762308510015465)
                    ·
                      refine ⟨3871652864071731382511599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162203818762308510015465 3871652864071731382511599)
                      ·
                        rfl

theorem cell23_7540017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_7540017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540017 prefixEnd_7540017 := by exact prefixLift 7540017
  have htrace : WordTrace (prefixWord ++ tailWord_7540017) baseStart_7540017 baseEnd_7540017 := by
    simpa [prefixWord, tailWord_7540017, baseEnd_7540017] using wordTrace_append hprefix tailTrace_7540017
  have hstable : (prefixWord ++ tailWord_7540017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540017).length < 2 ^ (prefixWord ++ tailWord_7540017).sum := by decide
  have hdescent : baseEnd_7540017 < baseStart_7540017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540023 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 8]
def baseStart_7540023 : Nat := 118140960795 + 7540023 * 2 ^ 59
def prefixEnd_7540023 : Nat := 4983230072969 + 3 ^ 40 * 7540023 * 2
def baseEnd_7540023 : Nat := 1290551981651886119678857

theorem tailTrace_7540023 : CollatzResearch.WordTrace tailWord_7540023 prefixEnd_7540023 1290551981651886119678857 := by
  unfold tailWord_7540023
  simp only [CollatzResearch.WordTrace]
  refine ⟨275007231562791879251816723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183338154375194586167877815 275007231562791879251816723)
  ·
    refine ⟨412510847344187818877725085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275007231562791879251816723 412510847344187818877725085)
    ·
      refine ⟨154691567754070432079146907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412510847344187818877725085 154691567754070432079146907)
      ·
        refine ⟨232037351631105648118720361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154691567754070432079146907 232037351631105648118720361)
        ·
          refine ⟨174028013723329236089040271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232037351631105648118720361 174028013723329236089040271)
          ·
            refine ⟨261042020584993854133560407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174028013723329236089040271 261042020584993854133560407)
            ·
              refine ⟨391563030877490781200340611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261042020584993854133560407 391563030877490781200340611)
              ·
                refine ⟨587344546316236171800510917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391563030877490781200340611 587344546316236171800510917)
                ·
                  refine ⟨110127102434294282212595797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587344546316236171800510917 110127102434294282212595797)
                  ·
                    refine ⟨1290551981651886119678857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110127102434294282212595797 1290551981651886119678857)
                    ·
                      rfl

theorem cell23_7540023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_7540023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540023 prefixEnd_7540023 := by exact prefixLift 7540023
  have htrace : WordTrace (prefixWord ++ tailWord_7540023) baseStart_7540023 baseEnd_7540023 := by
    simpa [prefixWord, tailWord_7540023, baseEnd_7540023] using wordTrace_append hprefix tailTrace_7540023
  have hstable : (prefixWord ++ tailWord_7540023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540023).length < 2 ^ (prefixWord ++ tailWord_7540023).sum := by decide
  have hdescent : baseEnd_7540023 < baseStart_7540023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540087 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 6]
def baseStart_7540087 : Nat := 118140960795 + 7540087 * 2 ^ 59
def prefixEnd_7540087 : Nat := 4983230072969 + 3 ^ 40 * 7540087 * 2
def baseEnd_7540087 : Nat := 430187645301949567626253

theorem tailTrace_7540087 : CollatzResearch.WordTrace tailWord_7540087 prefixEnd_7540087 430187645301949567626253 := by
  unfold tailWord_7540087
  simp only [CollatzResearch.WordTrace]
  refine ⟨275009565834560018182146515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183339710556373345454764343 275009565834560018182146515)
  ·
    refine ⟨412514348751840027273219773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275009565834560018182146515 412514348751840027273219773)
    ·
      refine ⟨154692880781940010227457415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412514348751840027273219773 154692880781940010227457415)
      ·
        refine ⟨232039321172910015341186123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154692880781940010227457415 232039321172910015341186123)
        ·
          refine ⟨348058981759365023011779185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232039321172910015341186123 348058981759365023011779185)
          ·
            refine ⟨261044236319523767258834389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348058981759365023011779185 261044236319523767258834389)
            ·
              refine ⟨6118224288738838295128931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 261044236319523767258834389 6118224288738838295128931)
              ·
                refine ⟨9177336433108257442693397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118224288738838295128931 9177336433108257442693397)
                ·
                  refine ⟨430187645301949567626253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9177336433108257442693397 430187645301949567626253)
                  ·
                    rfl

theorem cell23_7540087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 6].length) (baseStart_7540087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540087 prefixEnd_7540087 := by exact prefixLift 7540087
  have htrace : WordTrace (prefixWord ++ tailWord_7540087) baseStart_7540087 baseEnd_7540087 := by
    simpa [prefixWord, tailWord_7540087, baseEnd_7540087] using wordTrace_append hprefix tailTrace_7540087
  have hstable : (prefixWord ++ tailWord_7540087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540087).length < 2 ^ (prefixWord ++ tailWord_7540087).sum := by decide
  have hdescent : baseEnd_7540087 < baseStart_7540087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540107 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 5, 2]
def baseStart_7540107 : Nat := 118140960795 + 7540107 * 2 ^ 59
def prefixEnd_7540107 : Nat := 4983230072969 + 3 ^ 40 * 7540107 * 2
def baseEnd_7540107 : Nat := 3871699077330636030386185

theorem tailTrace_7540107 : CollatzResearch.WordTrace tailWord_7540107 prefixEnd_7540107 3871699077330636030386185 := by
  unfold tailWord_7540107
  simp only [CollatzResearch.WordTrace]
  refine ⟨275010295294487561597874575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183340196862991707731916383 275010295294487561597874575)
  ·
    refine ⟨412515442941731342396811863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275010295294487561597874575 412515442941731342396811863)
    ·
      refine ⟨618773164412597013595217795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412515442941731342396811863 618773164412597013595217795)
      ·
        refine ⟨928159746618895520392826693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618773164412597013595217795 928159746618895520392826693)
        ·
          refine ⟨174029952491042910073655005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 928159746618895520392826693 174029952491042910073655005)
          ·
            refine ⟨65261232184141091277620627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174029952491042910073655005 65261232184141091277620627)
            ·
              refine ⟨97891848276211636916430941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65261232184141091277620627 97891848276211636916430941)
              ·
                refine ⟨36709443103579363843661603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97891848276211636916430941 36709443103579363843661603)
                ·
                  refine ⟨55064164655369045765492405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36709443103579363843661603 55064164655369045765492405)
                  ·
                    refine ⟨5162265436440848040514913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55064164655369045765492405 5162265436440848040514913)
                    ·
                      refine ⟨3871699077330636030386185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162265436440848040514913 3871699077330636030386185)
                      ·
                        rfl

theorem cell23_7540107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5, 2].length) (baseStart_7540107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540107 prefixEnd_7540107 := by exact prefixLift 7540107
  have htrace : WordTrace (prefixWord ++ tailWord_7540107) baseStart_7540107 baseEnd_7540107 := by
    simpa [prefixWord, tailWord_7540107, baseEnd_7540107] using wordTrace_append hprefix tailTrace_7540107
  have hstable : (prefixWord ++ tailWord_7540107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540107).length < 2 ^ (prefixWord ++ tailWord_7540107).sum := by decide
  have hdescent : baseEnd_7540107 < baseStart_7540107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540117 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_7540117 : Nat := 118140960795 + 7540117 * 2 ^ 59
def prefixEnd_7540117 : Nat := 4983230072969 + 3 ^ 40 * 7540117 * 2
def baseEnd_7540117 : Nat := 1290568070712393663753713

theorem tailTrace_7540117 : CollatzResearch.WordTrace tailWord_7540117 prefixEnd_7540117 1290568070712393663753713 := by
  unfold tailWord_7540117
  simp only [CollatzResearch.WordTrace]
  refine ⟨275010660024451333305738605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183340440016300888870492403 275010660024451333305738605)
  ·
    refine ⟨103128997509169249989651977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275010660024451333305738605 103128997509169249989651977)
    ·
      refine ⟨77346748131876937492238983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103128997509169249989651977 77346748131876937492238983)
      ·
        refine ⟨116020122197815406238358475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77346748131876937492238983 116020122197815406238358475)
        ·
          refine ⟨174030183296723109357537713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116020122197815406238358475 174030183296723109357537713)
          ·
            refine ⟨130522637472542332018153285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174030183296723109357537713 130522637472542332018153285)
            ·
              refine ⟨24472994526101687253403741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130522637472542332018153285 24472994526101687253403741)
              ·
                refine ⟨9177372947288132720026403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24472994526101687253403741 9177372947288132720026403)
                ·
                  refine ⟨13766059420932199080039605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177372947288132720026403 13766059420932199080039605)
                  ·
                    refine ⟨1290568070712393663753713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13766059420932199080039605 1290568070712393663753713)
                    ·
                      rfl

theorem cell23_7540117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_7540117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540117 prefixEnd_7540117 := by exact prefixLift 7540117
  have htrace : WordTrace (prefixWord ++ tailWord_7540117) baseStart_7540117 baseEnd_7540117 := by
    simpa [prefixWord, tailWord_7540117, baseEnd_7540117] using wordTrace_append hprefix tailTrace_7540117
  have hstable : (prefixWord ++ tailWord_7540117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540117).length < 2 ^ (prefixWord ++ tailWord_7540117).sum := by decide
  have hdescent : baseEnd_7540117 < baseStart_7540117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540160 : List Nat := [2, 1, 1, 2, 3, 1, 4, 9]
def baseStart_7540160 : Nat := 118140960795 + 7540160 * 2 ^ 59
def prefixEnd_7540160 : Nat := 4983230072969 + 3 ^ 40 * 7540160 * 2
def baseEnd_7540160 : Nat := 143397270066863863815683

theorem tailTrace_7540160 : CollatzResearch.WordTrace tailWord_7540160 prefixEnd_7540160 143397270066863863815683 := by
  unfold tailWord_7540160
  simp only [CollatzResearch.WordTrace]
  refine ⟨137506114181647775824776967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183341485575530367766369289 137506114181647775824776967)
  ·
    refine ⟨206259171272471663737165451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137506114181647775824776967 206259171272471663737165451)
    ·
      refine ⟨309388756908707495605748177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206259171272471663737165451 309388756908707495605748177)
      ·
        refine ⟨232041567681530621704311133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309388756908707495605748177 232041567681530621704311133)
        ·
          refine ⟨87015587880573983139116675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232041567681530621704311133 87015587880573983139116675)
          ·
            refine ⟨130523381820860974708675013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87015587880573983139116675 130523381820860974708675013)
            ·
              refine ⟨24473134091411432757876565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130523381820860974708675013 24473134091411432757876565)
              ·
                refine ⟨143397270066863863815683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24473134091411432757876565 143397270066863863815683)
                ·
                  rfl

theorem cell23_7540160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 9].length) (baseStart_7540160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540160 prefixEnd_7540160 := by exact prefixLift 7540160
  have htrace : WordTrace (prefixWord ++ tailWord_7540160) baseStart_7540160 baseEnd_7540160 := by
    simpa [prefixWord, tailWord_7540160, baseEnd_7540160] using wordTrace_append hprefix tailTrace_7540160
  have hstable : (prefixWord ++ tailWord_7540160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540160).length < 2 ^ (prefixWord ++ tailWord_7540160).sum := by decide
  have hdescent : baseEnd_7540160 < baseStart_7540160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540164 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7540164 : Nat := 118140960795 + 7540164 * 2 ^ 59
def prefixEnd_7540164 : Nat := 4983230072969 + 3 ^ 40 * 7540164 * 2
def baseEnd_7540164 : Nat := 1290576115242647435791141

theorem tailTrace_7540164 : CollatzResearch.WordTrace tailWord_7540164 prefixEnd_7540164 1290576115242647435791141 := by
  unfold tailWord_7540164
  simp only [CollatzResearch.WordTrace]
  refine ⟨137506187127640530166349773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183341582836854040221799697 137506187127640530166349773)
  ·
    refine ⟨51564820172865198812381165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137506187127640530166349773 51564820172865198812381165)
    ·
      refine ⟨19336807564824449554642937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51564820172865198812381165 19336807564824449554642937)
      ·
        refine ⟨14502605673618337165982203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19336807564824449554642937 14502605673618337165982203)
        ·
          refine ⟨21753908510427505748973305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14502605673618337165982203 21753908510427505748973305)
          ·
            refine ⟨16315431382820629311729979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21753908510427505748973305 16315431382820629311729979)
            ·
              refine ⟨24473147074230943967594969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16315431382820629311729979 24473147074230943967594969)
              ·
                refine ⟨18354860305673207975696227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24473147074230943967594969 18354860305673207975696227)
                ·
                  refine ⟨27532290458509811963544341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18354860305673207975696227 27532290458509811963544341)
                  ·
                    refine ⟨1290576115242647435791141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27532290458509811963544341 1290576115242647435791141)
                    ·
                      rfl

theorem cell23_7540164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7540164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540164 prefixEnd_7540164 := by exact prefixLift 7540164
  have htrace : WordTrace (prefixWord ++ tailWord_7540164) baseStart_7540164 baseEnd_7540164 := by
    simpa [prefixWord, tailWord_7540164, baseEnd_7540164] using wordTrace_append hprefix tailTrace_7540164
  have hstable : (prefixWord ++ tailWord_7540164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540164).length < 2 ^ (prefixWord ++ tailWord_7540164).sum := by decide
  have hdescent : baseEnd_7540164 < baseStart_7540164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540167 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_7540167 : Nat := 118140960795 + 7540167 * 2 ^ 59
def prefixEnd_7540167 : Nat := 4983230072969 + 3 ^ 40 * 7540167 * 2
def baseEnd_7540167 : Nat := 3871729886169905795635909

theorem tailTrace_7540167 : CollatzResearch.WordTrace tailWord_7540167 prefixEnd_7540167 3871729886169905795635909 := by
  unfold tailWord_7540167
  simp only [CollatzResearch.WordTrace]
  refine ⟨275012483674270191845058755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183341655782846794563372503 275012483674270191845058755)
  ·
    refine ⟨412518725511405287767588133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275012483674270191845058755 412518725511405287767588133)
    ·
      refine ⟨77347261033388491456422775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412518725511405287767588133 77347261033388491456422775)
      ·
        refine ⟨116020891550082737184634163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77347261033388491456422775 116020891550082737184634163)
        ·
          refine ⟨174031337325124105776951245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116020891550082737184634163 174031337325124105776951245)
          ·
            refine ⟨65261751496921539666356717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174031337325124105776951245 65261751496921539666356717)
            ·
              refine ⟨24473156811345577374883769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65261751496921539666356717 24473156811345577374883769)
              ·
                refine ⟨18354867608509183031162827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24473156811345577374883769 18354867608509183031162827)
                ·
                  refine ⟨27532301412763774546744241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18354867608509183031162827 27532301412763774546744241)
                  ·
                    refine ⟨20649226059572830910058181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27532301412763774546744241 20649226059572830910058181)
                    ·
                      refine ⟨3871729886169905795635909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20649226059572830910058181 3871729886169905795635909)
                      ·
                        rfl

theorem cell23_7540167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_7540167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540167 prefixEnd_7540167 := by exact prefixLift 7540167
  have htrace : WordTrace (prefixWord ++ tailWord_7540167) baseStart_7540167 baseEnd_7540167 := by
    simpa [prefixWord, tailWord_7540167, baseEnd_7540167] using wordTrace_append hprefix tailTrace_7540167
  have hstable : (prefixWord ++ tailWord_7540167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540167).length < 2 ^ (prefixWord ++ tailWord_7540167).sum := by decide
  have hdescent : baseEnd_7540167 < baseStart_7540167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540174 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_7540174 : Nat := 118140960795 + 7540174 * 2 ^ 59
def prefixEnd_7540174 : Nat := 4983230072969 + 3 ^ 40 * 7540174 * 2
def baseEnd_7540174 : Nat := 3871733480534487268248377

theorem tailTrace_7540174 : CollatzResearch.WordTrace tailWord_7540174 prefixEnd_7540174 3871733480534487268248377 := by
  unfold tailWord_7540174
  simp only [CollatzResearch.WordTrace]
  refine ⟨34376592373155604005070447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183341825990163221360375717 34376592373155604005070447)
  ·
    refine ⟨51564888559733406007605671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34376592373155604005070447 51564888559733406007605671)
    ·
      refine ⟨77347332839600109011408507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51564888559733406007605671 77347332839600109011408507)
      ·
        refine ⟨116020999259400163517112761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77347332839600109011408507 116020999259400163517112761)
        ·
          refine ⟨87015749444550122637834571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116020999259400163517112761 87015749444550122637834571)
          ·
            refine ⟨130523624166825183956751857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87015749444550122637834571 130523624166825183956751857)
            ·
              refine ⟨97892718125118887967563893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130523624166825183956751857 97892718125118887967563893)
              ·
                refine ⟨9177442324229895746959115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97892718125118887967563893 9177442324229895746959115)
                ·
                  refine ⟨13766163486344843620438673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177442324229895746959115 13766163486344843620438673)
                  ·
                    refine ⟨10324622614758632715329005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13766163486344843620438673 10324622614758632715329005)
                    ·
                      refine ⟨3871733480534487268248377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324622614758632715329005 3871733480534487268248377)
                      ·
                        rfl

theorem cell23_7540174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_7540174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540174 prefixEnd_7540174 := by exact prefixLift 7540174
  have htrace : WordTrace (prefixWord ++ tailWord_7540174) baseStart_7540174 baseEnd_7540174 := by
    simpa [prefixWord, tailWord_7540174, baseEnd_7540174] using wordTrace_append hprefix tailTrace_7540174
  have hstable : (prefixWord ++ tailWord_7540174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540174).length < 2 ^ (prefixWord ++ tailWord_7540174).sum := by decide
  have hdescent : baseEnd_7540174 < baseStart_7540174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540182 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_7540182 : Nat := 118140960795 + 7540182 * 2 ^ 59
def prefixEnd_7540182 : Nat := 4983230072969 + 3 ^ 40 * 7540182 * 2
def baseEnd_7540182 : Nat := 3871737588379723236948341

theorem tailTrace_7540182 : CollatzResearch.WordTrace tailWord_7540182 prefixEnd_7540182 3871737588379723236948341 := by
  unfold tailWord_7540182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17188314423075990587928425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183342020512810566271236533 17188314423075990587928425)
  ·
    refine ⟨12891235817306992940946319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17188314423075990587928425 12891235817306992940946319)
    ·
      refine ⟨19336853725960489411419479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12891235817306992940946319 19336853725960489411419479)
      ·
        refine ⟨29005280588940734117129219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19336853725960489411419479 29005280588940734117129219)
        ·
          refine ⟨43507920883411101175693829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29005280588940734117129219 43507920883411101175693829)
          ·
            refine ⟨8157735165639581470442593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43507920883411101175693829 8157735165639581470442593)
            ·
              refine ⟨6118301374229686102831945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157735165639581470442593 6118301374229686102831945)
              ·
                refine ⟨4588726030672264577123959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118301374229686102831945 4588726030672264577123959)
                ·
                  refine ⟨6883089046008396865685939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588726030672264577123959 6883089046008396865685939)
                  ·
                    refine ⟨10324633569012595298528909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6883089046008396865685939 10324633569012595298528909)
                    ·
                      refine ⟨3871737588379723236948341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324633569012595298528909 3871737588379723236948341)
                      ·
                        rfl

theorem cell23_7540182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_7540182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540182 prefixEnd_7540182 := by exact prefixLift 7540182
  have htrace : WordTrace (prefixWord ++ tailWord_7540182) baseStart_7540182 baseEnd_7540182 := by
    simpa [prefixWord, tailWord_7540182, baseEnd_7540182] using wordTrace_append hprefix tailTrace_7540182
  have hstable : (prefixWord ++ tailWord_7540182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540182).length < 2 ^ (prefixWord ++ tailWord_7540182).sum := by decide
  have hdescent : baseEnd_7540182 < baseStart_7540182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540222 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7540222 : Nat := 118140960795 + 7540222 * 2 ^ 59
def prefixEnd_7540222 : Nat := 4983230072969 + 3 ^ 40 * 7540222 * 2
def baseEnd_7540222 : Nat := 3871758127605903080448157

theorem tailTrace_7540222 : CollatzResearch.WordTrace tailWord_7540222 prefixEnd_7540222 3871758127605903080448157 := by
  unfold tailWord_7540222
  simp only [CollatzResearch.WordTrace]
  refine ⟨34376811211133867029788865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183342993126047290825540613 34376811211133867029788865)
  ·
    refine ⟨25782608408350400272341649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34376811211133867029788865 25782608408350400272341649)
    ·
      refine ⟨19336956306262800204256237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25782608408350400272341649 19336956306262800204256237)
      ·
        refine ⟨7251358614848550076596089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19336956306262800204256237 7251358614848550076596089)
        ·
          refine ⟨5438518961136412557447067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7251358614848550076596089 5438518961136412557447067)
          ·
            refine ⟨8157778441704618836170601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438518961136412557447067 8157778441704618836170601)
            ·
              refine ⟨6118333831278464127127951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157778441704618836170601 6118333831278464127127951)
              ·
                refine ⟨9177500746917696190691927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118333831278464127127951 9177500746917696190691927)
                ·
                  refine ⟨13766251120376544286037891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177500746917696190691927 13766251120376544286037891)
                  ·
                    refine ⟨20649376680564816429056837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13766251120376544286037891 20649376680564816429056837)
                    ·
                      refine ⟨3871758127605903080448157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20649376680564816429056837 3871758127605903080448157)
                      ·
                        rfl

theorem cell23_7540222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7540222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540222 prefixEnd_7540222 := by exact prefixLift 7540222
  have htrace : WordTrace (prefixWord ++ tailWord_7540222) baseStart_7540222 baseEnd_7540222 := by
    simpa [prefixWord, tailWord_7540222, baseEnd_7540222] using wordTrace_append hprefix tailTrace_7540222
  have hstable : (prefixWord ++ tailWord_7540222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540222).length < 2 ^ (prefixWord ++ tailWord_7540222).sum := by decide
  have hdescent : baseEnd_7540222 < baseStart_7540222 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540225 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_7540225 : Nat := 118140960795 + 7540225 * 2 ^ 59
def prefixEnd_7540225 : Nat := 4983230072969 + 3 ^ 40 * 7540225 * 2
def baseEnd_7540225 : Nat := 3871759668047866568710643

theorem tailTrace_7540225 : CollatzResearch.WordTrace tailWord_7540225 prefixEnd_7540225 3871759668047866568710643 := by
  unfold tailWord_7540225
  simp only [CollatzResearch.WordTrace]
  refine ⟨275014599108060067750670129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183343066072040045167113419 275014599108060067750670129)
  ·
    refine ⟨206260949331045050813002597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275014599108060067750670129 206260949331045050813002597)
    ·
      refine ⟨38673927999570947027437987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206260949331045050813002597 38673927999570947027437987)
      ·
        refine ⟨58010891999356420541156981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38673927999570947027437987 58010891999356420541156981)
        ·
          refine ⟨5438521124939664425733467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58010891999356420541156981 5438521124939664425733467)
          ·
            refine ⟨8157781687409496638600201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438521124939664425733467 8157781687409496638600201)
            ·
              refine ⟨6118336265557122478950151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8157781687409496638600201 6118336265557122478950151)
              ·
                refine ⟨9177504398335683718425227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6118336265557122478950151 9177504398335683718425227)
                ·
                  refine ⟨13766256597503525577637841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177504398335683718425227 13766256597503525577637841)
                  ·
                    refine ⟨10324692448127644183228381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13766256597503525577637841 10324692448127644183228381)
                    ·
                      refine ⟨3871759668047866568710643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324692448127644183228381 3871759668047866568710643)
                      ·
                        rfl

theorem cell23_7540225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_7540225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540225 prefixEnd_7540225 := by exact prefixLift 7540225
  have htrace : WordTrace (prefixWord ++ tailWord_7540225) baseStart_7540225 baseEnd_7540225 := by
    simpa [prefixWord, tailWord_7540225, baseEnd_7540225] using wordTrace_append hprefix tailTrace_7540225
  have hstable : (prefixWord ++ tailWord_7540225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540225).length < 2 ^ (prefixWord ++ tailWord_7540225).sum := by decide
  have hdescent : baseEnd_7540225 < baseStart_7540225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540304 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2]
def baseStart_7540304 : Nat := 118140960795 + 7540304 * 2 ^ 59
def prefixEnd_7540304 : Nat := 4983230072969 + 3 ^ 40 * 7540304 * 2
def baseEnd_7540304 : Nat := 3871800233019571759622779

theorem tailTrace_7540304 : CollatzResearch.WordTrace tailWord_7540304 prefixEnd_7540304 3871800233019571759622779 := by
  unfold tailWord_7540304
  simp only [CollatzResearch.WordTrace]
  refine ⟨137508740237386932121397983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183344986983182576161863977 137508740237386932121397983)
  ·
    refine ⟨206263110356080398182096975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137508740237386932121397983 206263110356080398182096975)
    ·
      refine ⟨309394665534120597273145463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206263110356080398182096975 309394665534120597273145463)
      ·
        refine ⟨464091998301180895909718195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309394665534120597273145463 464091998301180895909718195)
        ·
          refine ⟨696137997451771343864577293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464091998301180895909718195 696137997451771343864577293)
          ·
            refine ⟨261051749044414253949216485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696137997451771343864577293 261051749044414253949216485)
            ·
              refine ⟨48947202945827672615478091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261051749044414253949216485 48947202945827672615478091)
              ·
                refine ⟨73420804418741508923217137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48947202945827672615478091 73420804418741508923217137)
                ·
                  refine ⟨55065603314056131692412853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73420804418741508923217137 55065603314056131692412853)
                  ·
                    refine ⟨5162400310692762346163705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55065603314056131692412853 5162400310692762346163705)
                    ·
                      refine ⟨3871800233019571759622779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162400310692762346163705 3871800233019571759622779)
                      ·
                        rfl

theorem cell23_7540304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2].length) (baseStart_7540304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540304 prefixEnd_7540304 := by exact prefixLift 7540304
  have htrace : WordTrace (prefixWord ++ tailWord_7540304) baseStart_7540304 baseEnd_7540304 := by
    simpa [prefixWord, tailWord_7540304, baseEnd_7540304] using wordTrace_append hprefix tailTrace_7540304
  have hstable : (prefixWord ++ tailWord_7540304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540304).length < 2 ^ (prefixWord ++ tailWord_7540304).sum := by decide
  have hdescent : baseEnd_7540304 < baseStart_7540304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540327 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 8]
def baseStart_7540327 : Nat := 118140960795 + 7540327 * 2 ^ 59
def prefixEnd_7540327 : Nat := 4983230072969 + 3 ^ 40 * 7540327 * 2
def baseEnd_7540327 : Nat := 1290604014358208389878391

theorem tailTrace_7540327 : CollatzResearch.WordTrace tailWord_7540327 prefixEnd_7540327 1290604014358208389878391 := by
  unfold tailWord_7540327
  simp only [CollatzResearch.WordTrace]
  refine ⟨275018319353690539170883235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183345546235793692780588823 275018319353690539170883235)
  ·
    refine ⟨412527479030535808756324853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275018319353690539170883235 412527479030535808756324853)
    ·
      refine ⟨38674451159112732070905455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 412527479030535808756324853 38674451159112732070905455)
      ·
        refine ⟨58011676738669098106358183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38674451159112732070905455 58011676738669098106358183)
        ·
          refine ⟨87017515108003647159537275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58011676738669098106358183 87017515108003647159537275)
          ·
            refine ⟨130526272662005470739305913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87017515108003647159537275 130526272662005470739305913)
            ·
              refine ⟨97894704496504103054479435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130526272662005470739305913 97894704496504103054479435)
              ·
                refine ⟨146842056744756154581719153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97894704496504103054479435 146842056744756154581719153)
                ·
                  refine ⟨110131542558567115936289365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146842056744756154581719153 110131542558567115936289365)
                  ·
                    refine ⟨1290604014358208389878391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110131542558567115936289365 1290604014358208389878391)
                    ·
                      rfl

theorem cell23_7540327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_7540327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540327 prefixEnd_7540327 := by exact prefixLift 7540327
  have htrace : WordTrace (prefixWord ++ tailWord_7540327) baseStart_7540327 baseEnd_7540327 := by
    simpa [prefixWord, tailWord_7540327, baseEnd_7540327] using wordTrace_append hprefix tailTrace_7540327
  have hstable : (prefixWord ++ tailWord_7540327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540327).length < 2 ^ (prefixWord ++ tailWord_7540327).sum := by decide
  have hdescent : baseEnd_7540327 < baseStart_7540327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540347 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_7540347 : Nat := 118140960795 + 7540347 * 2 ^ 59
def prefixEnd_7540347 : Nat := 4983230072969 + 3 ^ 40 * 7540347 * 2
def baseEnd_7540347 : Nat := 3871822312687715091385081

theorem tailTrace_7540347 : CollatzResearch.WordTrace tailWord_7540347 prefixEnd_7540347 3871822312687715091385081 := by
  unfold tailWord_7540347
  simp only [CollatzResearch.WordTrace]
  refine ⟨275019048813618082586611295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183346032542412055057740863 275019048813618082586611295)
  ·
    refine ⟨412528573220427123879916943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275019048813618082586611295 412528573220427123879916943)
    ·
      refine ⟨618792859830640685819875415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412528573220427123879916943 618792859830640685819875415)
      ·
        refine ⟨928189289745961028729813123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618792859830640685819875415 928189289745961028729813123)
        ·
          refine ⟨1392283934618941543094719685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928189289745961028729813123 1392283934618941543094719685)
          ·
            refine ⟨261053237741051539330259941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1392283934618941543094719685 261053237741051539330259941)
            ·
              refine ⟨48947482076447163624423739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261053237741051539330259941 48947482076447163624423739)
              ·
                refine ⟨73421223114670745436635609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48947482076447163624423739 73421223114670745436635609)
                ·
                  refine ⟨55065917336003059077476707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73421223114670745436635609 55065917336003059077476707)
                  ·
                    refine ⟨82598876004004588616215061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55065917336003059077476707 82598876004004588616215061)
                    ·
                      refine ⟨3871822312687715091385081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82598876004004588616215061 3871822312687715091385081)
                      ·
                        rfl

theorem cell23_7540347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_7540347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540347 prefixEnd_7540347 := by exact prefixLift 7540347
  have htrace : WordTrace (prefixWord ++ tailWord_7540347) baseStart_7540347 baseEnd_7540347 := by
    simpa [prefixWord, tailWord_7540347, baseEnd_7540347] using wordTrace_append hprefix tailTrace_7540347
  have hstable : (prefixWord ++ tailWord_7540347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540347).length < 2 ^ (prefixWord ++ tailWord_7540347).sum := by decide
  have hdescent : baseEnd_7540347 < baseStart_7540347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540377 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_7540377 : Nat := 118140960795 + 7540377 * 2 ^ 59
def prefixEnd_7540377 : Nat := 4983230072969 + 3 ^ 40 * 7540377 * 2
def baseEnd_7540377 : Nat := 3871837717107349974009943

theorem tailTrace_7540377 : CollatzResearch.WordTrace tailWord_7540377 prefixEnd_7540377 3871837717107349974009943 := by
  unfold tailWord_7540377
  simp only [CollatzResearch.WordTrace]
  refine ⟨275020143003509397710203385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183346762002339598473468923 275020143003509397710203385)
  ·
    refine ⟨206265107252632048282652539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275020143003509397710203385 206265107252632048282652539)
    ·
      refine ⟨309397660878948072423978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206265107252632048282652539 309397660878948072423978809)
      ·
        refine ⟨232048245659211054317984107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309397660878948072423978809 232048245659211054317984107)
        ·
          refine ⟨348072368488816581476976161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232048245659211054317984107 348072368488816581476976161)
          ·
            refine ⟨261054276366612436107732121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348072368488816581476976161 261054276366612436107732121)
            ·
              refine ⟨195790707274959327080799091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261054276366612436107732121 195790707274959327080799091)
              ·
                refine ⟨293686060912438990621198637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195790707274959327080799091 293686060912438990621198637)
                ·
                  refine ⟨110132272842164621482949489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293686060912438990621198637 110132272842164621482949489)
                  ·
                    refine ⟨82599204631623466112212117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110132272842164621482949489 82599204631623466112212117)
                    ·
                      refine ⟨3871837717107349974009943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82599204631623466112212117 3871837717107349974009943)
                      ·
                        rfl

theorem cell23_7540377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_7540377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540377 prefixEnd_7540377 := by exact prefixLift 7540377
  have htrace : WordTrace (prefixWord ++ tailWord_7540377) baseStart_7540377 baseEnd_7540377 := by
    simpa [prefixWord, tailWord_7540377, baseEnd_7540377] using wordTrace_append hprefix tailTrace_7540377
  have hstable : (prefixWord ++ tailWord_7540377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540377).length < 2 ^ (prefixWord ++ tailWord_7540377).sum := by decide
  have hdescent : baseEnd_7540377 < baseStart_7540377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540388 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_7540388 : Nat := 118140960795 + 7540388 * 2 ^ 59
def prefixEnd_7540388 : Nat := 4983230072969 + 3 ^ 40 * 7540388 * 2
def baseEnd_7540388 : Nat := 3871843365394549430972393

theorem tailTrace_7540388 : CollatzResearch.WordTrace tailWord_7540388 prefixEnd_7540388 3871843365394549430972393 := by
  unfold tailWord_7540388
  simp only [CollatzResearch.WordTrace]
  refine ⟨137510272103234773294426909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183347029470979697725902545 137510272103234773294426909)
  ·
    refine ⟨51566352038713039985410091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137510272103234773294426909 51566352038713039985410091)
    ·
      refine ⟨77349528058069559978115137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51566352038713039985410091 77349528058069559978115137)
      ·
        refine ⟨58012146043552169983586353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77349528058069559978115137 58012146043552169983586353)
        ·
          refine ⟨43509109532664127487689765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58012146043552169983586353 43509109532664127487689765)
          ·
            refine ⟨8157958037374523903941831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43509109532664127487689765 8157958037374523903941831)
            ·
              refine ⟨12236937056061785855912747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8157958037374523903941831 12236937056061785855912747)
              ·
                refine ⟨18355405584092678783869121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12236937056061785855912747 18355405584092678783869121)
                ·
                  refine ⟨13766554188069509087901841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18355405584092678783869121 13766554188069509087901841)
                  ·
                    refine ⟨10324915641052131815926381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13766554188069509087901841 10324915641052131815926381)
                    ·
                      refine ⟨3871843365394549430972393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10324915641052131815926381 3871843365394549430972393)
                      ·
                        rfl

theorem cell23_7540388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_7540388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540388 prefixEnd_7540388 := by exact prefixLift 7540388
  have htrace : WordTrace (prefixWord ++ tailWord_7540388) baseStart_7540388 baseEnd_7540388 := by
    simpa [prefixWord, tailWord_7540388, baseEnd_7540388] using wordTrace_append hprefix tailTrace_7540388
  have hstable : (prefixWord ++ tailWord_7540388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540388).length < 2 ^ (prefixWord ++ tailWord_7540388).sum := by decide
  have hdescent : baseEnd_7540388 < baseStart_7540388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540411 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 2, 3, 2]
def baseStart_7540411 : Nat := 118140960795 + 7540411 * 2 ^ 59
def prefixEnd_7540411 : Nat := 4983230072969 + 3 ^ 40 * 7540411 * 2
def baseEnd_7540411 : Nat := 3871855175449602840984787

theorem tailTrace_7540411 : CollatzResearch.WordTrace tailWord_7540411 prefixEnd_7540411 3871855175449602840984787 := by
  unfold tailWord_7540411
  simp only [CollatzResearch.WordTrace]
  refine ⟨275021383085386221516941087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183347588723590814344627391 275021383085386221516941087)
  ·
    refine ⟨412532074628079332275411631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275021383085386221516941087 412532074628079332275411631)
    ·
      refine ⟨618798111942118998413117447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412532074628079332275411631 618798111942118998413117447)
      ·
        refine ⟨928197167913178497619676171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618798111942118998413117447 928197167913178497619676171)
        ·
          refine ⟨1392295751869767746429514257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928197167913178497619676171 1392295751869767746429514257)
          ·
            refine ⟨1044221813902325809822135693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392295751869767746429514257 1044221813902325809822135693)
            ·
              refine ⟨391583180213372178683300885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1044221813902325809822135693 391583180213372178683300885)
              ·
                refine ⟨18355461572501820875779729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391583180213372178683300885 18355461572501820875779729)
                ·
                  refine ⟨13766596179376365656834797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18355461572501820875779729 13766596179376365656834797)
                  ·
                    refine ⟨5162473567266137121313049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13766596179376365656834797 5162473567266137121313049)
                    ·
                      refine ⟨3871855175449602840984787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162473567266137121313049 3871855175449602840984787)
                      ·
                        rfl

theorem cell23_7540411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3, 2].length) (baseStart_7540411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540411 prefixEnd_7540411 := by exact prefixLift 7540411
  have htrace : WordTrace (prefixWord ++ tailWord_7540411) baseStart_7540411 baseEnd_7540411 := by
    simpa [prefixWord, tailWord_7540411, baseEnd_7540411] using wordTrace_append hprefix tailTrace_7540411
  have hstable : (prefixWord ++ tailWord_7540411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540411).length < 2 ^ (prefixWord ++ tailWord_7540411).sum := by decide
  have hdescent : baseEnd_7540411 < baseStart_7540411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540441 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_7540441 : Nat := 118140960795 + 7540441 * 2 ^ 59
def prefixEnd_7540441 : Nat := 4983230072969 + 3 ^ 40 * 7540441 * 2
def baseEnd_7540441 : Nat := 3871870579869237723609649

theorem tailTrace_7540441 : CollatzResearch.WordTrace tailWord_7540441 prefixEnd_7540441 3871870579869237723609649 := by
  unfold tailWord_7540441
  simp only [CollatzResearch.WordTrace]
  refine ⟨275022477275277536640533177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183348318183518357760355451 275022477275277536640533177)
  ·
    refine ⟨206266857956458152480399883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275022477275277536640533177 206266857956458152480399883)
    ·
      refine ⟨309400286934687228720599825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206266857956458152480399883 309400286934687228720599825)
      ·
        refine ⟨232050215201015421540449869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309400286934687228720599825 232050215201015421540449869)
        ·
          refine ⟨87018830700380783077668701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232050215201015421540449869 87018830700380783077668701)
          ·
            refine ⟨32632061512642793654125763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87018830700380783077668701 32632061512642793654125763)
            ·
              refine ⟨48948092268964190481188645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32632061512642793654125763 48948092268964190481188645)
              ·
                refine ⟨9177767300430785715222871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48948092268964190481188645 9177767300430785715222871)
                ·
                  refine ⟨13766650950646178572834307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9177767300430785715222871 13766650950646178572834307)
                  ·
                    refine ⟨20649976425969267859251461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13766650950646178572834307 20649976425969267859251461)
                    ·
                      refine ⟨3871870579869237723609649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20649976425969267859251461 3871870579869237723609649)
                      ·
                        rfl

theorem cell23_7540441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_7540441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540441 prefixEnd_7540441 := by exact prefixLift 7540441
  have htrace : WordTrace (prefixWord ++ tailWord_7540441) baseStart_7540441 baseEnd_7540441 := by
    simpa [prefixWord, tailWord_7540441, baseEnd_7540441] using wordTrace_append hprefix tailTrace_7540441
  have hstable : (prefixWord ++ tailWord_7540441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540441).length < 2 ^ (prefixWord ++ tailWord_7540441).sum := by decide
  have hdescent : baseEnd_7540441 < baseStart_7540441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540458 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_7540458 : Nat := 118140960795 + 7540458 * 2 ^ 59
def prefixEnd_7540458 : Nat := 4983230072969 + 3 ^ 40 * 7540458 * 2
def baseEnd_7540458 : Nat := 3871879309040364157097071

theorem tailTrace_7540458 : CollatzResearch.WordTrace tailWord_7540458 prefixEnd_7540458 3871879309040364157097071 := by
  unfold tailWord_7540458
  simp only [CollatzResearch.WordTrace]
  refine ⟨68755774329053987135975507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183348731544143965695934685 68755774329053987135975507)
  ·
    refine ⟨103133661493580980703963261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68755774329053987135975507 103133661493580980703963261)
    ·
      refine ⟨38675123060092867763986223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103133661493580980703963261 38675123060092867763986223)
      ·
        refine ⟨58012684590139301645979335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38675123060092867763986223 58012684590139301645979335)
        ·
          refine ⟨87019026885208952468969003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58012684590139301645979335 87019026885208952468969003)
          ·
            refine ⟨130528540327813428703453505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87019026885208952468969003 130528540327813428703453505)
            ·
              refine ⟨97896405245860071527590129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130528540327813428703453505 97896405245860071527590129)
              ·
                refine ⟨73422303934395053645692597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97896405245860071527590129 73422303934395053645692597)
                ·
                  refine ⟨6883340993849536279283681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73422303934395053645692597 6883340993849536279283681)
                  ·
                    refine ⟨5162505745387152209462761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6883340993849536279283681 5162505745387152209462761)
                    ·
                      refine ⟨3871879309040364157097071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162505745387152209462761 3871879309040364157097071)
                      ·
                        rfl

theorem cell23_7540458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_7540458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540458 prefixEnd_7540458 := by exact prefixLift 7540458
  have htrace : WordTrace (prefixWord ++ tailWord_7540458) baseStart_7540458 baseEnd_7540458 := by
    simpa [prefixWord, tailWord_7540458, baseEnd_7540458] using wordTrace_append hprefix tailTrace_7540458
  have hstable : (prefixWord ++ tailWord_7540458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540458).length < 2 ^ (prefixWord ++ tailWord_7540458).sum := by decide
  have hdescent : baseEnd_7540458 < baseStart_7540458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540461 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7540461 : Nat := 118140960795 + 7540461 * 2 ^ 59
def prefixEnd_7540461 : Nat := 4983230072969 + 3 ^ 40 * 7540461 * 2
def baseEnd_7540461 : Nat := 3871880849482327645359557

theorem tailTrace_7540461 : CollatzResearch.WordTrace tailWord_7540461 prefixEnd_7540461 3871880849482327645359557 := by
  unfold tailWord_7540461
  simp only [CollatzResearch.WordTrace]
  refine ⟨275023206735205080056261237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183348804490136720037507491 275023206735205080056261237)
  ·
    refine ⟨25783425631425476255274491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275023206735205080056261237 25783425631425476255274491)
    ·
      refine ⟨38675138447138214382911737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25783425631425476255274491 38675138447138214382911737)
      ·
        refine ⟨29006353835353660787183803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38675138447138214382911737 29006353835353660787183803)
        ·
          refine ⟨43509530753030491180775705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29006353835353660787183803 43509530753030491180775705)
          ·
            refine ⟨32632148064772868385581779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43509530753030491180775705 32632148064772868385581779)
            ·
              refine ⟨48948222097159302578372669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32632148064772868385581779 48948222097159302578372669)
              ·
                refine ⟨18355583286434738466889751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48948222097159302578372669 18355583286434738466889751)
                ·
                  refine ⟨27533374929652107700334627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18355583286434738466889751 27533374929652107700334627)
                  ·
                    refine ⟨41300062394478161550501941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27533374929652107700334627 41300062394478161550501941)
                    ·
                      refine ⟨3871880849482327645359557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41300062394478161550501941 3871880849482327645359557)
                      ·
                        rfl

theorem cell23_7540461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7540461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540461 prefixEnd_7540461 := by exact prefixLift 7540461
  have htrace : WordTrace (prefixWord ++ tailWord_7540461) baseStart_7540461 baseEnd_7540461 := by
    simpa [prefixWord, tailWord_7540461, baseEnd_7540461] using wordTrace_append hprefix tailTrace_7540461
  have hstable : (prefixWord ++ tailWord_7540461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540461).length < 2 ^ (prefixWord ++ tailWord_7540461).sum := by decide
  have hdescent : baseEnd_7540461 < baseStart_7540461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540504 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7540504 : Nat := 118140960795 + 7540504 * 2 ^ 59
def prefixEnd_7540504 : Nat := 4983230072969 + 3 ^ 40 * 7540504 * 2
def baseEnd_7540504 : Nat := 3871902929150470977121859

theorem tailTrace_7540504 : CollatzResearch.WordTrace tailWord_7540504 prefixEnd_7540504 3871902929150470977121859 := by
  unfold tailWord_7540504
  simp only [CollatzResearch.WordTrace]
  refine ⟨137512387537024649200038283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183349850049366198933384377 137512387537024649200038283)
  ·
    refine ⟨206268581305536973800057425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137512387537024649200038283 206268581305536973800057425)
    ·
      refine ⟨154701435979152730350043069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206268581305536973800057425 154701435979152730350043069)
      ·
        refine ⟨58013038492182273881266151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154701435979152730350043069 58013038492182273881266151)
        ·
          refine ⟨87019557738273410821899227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58013038492182273881266151 87019557738273410821899227)
          ·
            refine ⟨130529336607410116232848841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87019557738273410821899227 130529336607410116232848841)
            ·
              refine ⟨97897002455557587174636631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130529336607410116232848841 97897002455557587174636631)
              ·
                refine ⟨146845503683336380761954947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97897002455557587174636631 146845503683336380761954947)
                ·
                  refine ⟨220268255525004571142932421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146845503683336380761954947 220268255525004571142932421)
                  ·
                    refine ⟨41300297910938357089299829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220268255525004571142932421 41300297910938357089299829)
                    ·
                      refine ⟨3871902929150470977121859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41300297910938357089299829 3871902929150470977121859)
                      ·
                        rfl

theorem cell23_7540504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7540504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540504 prefixEnd_7540504 := by exact prefixLift 7540504
  have htrace : WordTrace (prefixWord ++ tailWord_7540504) baseStart_7540504 baseEnd_7540504 := by
    simpa [prefixWord, tailWord_7540504, baseEnd_7540504] using wordTrace_append hprefix tailTrace_7540504
  have hstable : (prefixWord ++ tailWord_7540504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540504).length < 2 ^ (prefixWord ++ tailWord_7540504).sum := by decide
  have hdescent : baseEnd_7540504 < baseStart_7540504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540541 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_7540541 : Nat := 118140960795 + 7540541 * 2 ^ 59
def prefixEnd_7540541 : Nat := 4983230072969 + 3 ^ 40 * 7540541 * 2
def baseEnd_7540541 : Nat := 1290640642644895777453063

theorem tailTrace_7540541 : CollatzResearch.WordTrace tailWord_7540541 prefixEnd_7540541 1290640642644895777453063 := by
  unfold tailWord_7540541
  simp only [CollatzResearch.WordTrace]
  refine ⟨275026124574915253719173477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183350749716610169146115651 275026124574915253719173477)
  ·
    refine ⟨51567398357796610072345027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275026124574915253719173477 51567398357796610072345027)
    ·
      refine ⟨77351097536694915108517541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51567398357796610072345027 77351097536694915108517541)
      ·
        refine ⟨14503330788130296582847039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77351097536694915108517541 14503330788130296582847039)
        ·
          refine ⟨21754996182195444874270559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14503330788130296582847039 21754996182195444874270559)
          ·
            refine ⟨32632494273293167311405839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21754996182195444874270559 32632494273293167311405839)
            ·
              refine ⟨48948741409939750967108759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32632494273293167311405839 48948741409939750967108759)
              ·
                refine ⟨73423112114909626450663139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48948741409939750967108759 73423112114909626450663139)
                ·
                  refine ⟨110134668172364439675994709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73423112114909626450663139 110134668172364439675994709)
                  ·
                    refine ⟨1290640642644895777453063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110134668172364439675994709 1290640642644895777453063)
                    ·
                      rfl

theorem cell23_7540541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_7540541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540541 prefixEnd_7540541 := by exact prefixLift 7540541
  have htrace : WordTrace (prefixWord ++ tailWord_7540541) baseStart_7540541 baseEnd_7540541 := by
    simpa [prefixWord, tailWord_7540541, baseEnd_7540541] using wordTrace_append hprefix tailTrace_7540541
  have hstable : (prefixWord ++ tailWord_7540541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540541).length < 2 ^ (prefixWord ++ tailWord_7540541).sum := by decide
  have hdescent : baseEnd_7540541 < baseStart_7540541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540578 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7540578 : Nat := 118140960795 + 7540578 * 2 ^ 59
def prefixEnd_7540578 : Nat := 4983230072969 + 3 ^ 40 * 7540578 * 2
def baseEnd_7540578 : Nat := 3871940926718903687596519

theorem tailTrace_7540578 : CollatzResearch.WordTrace tailWord_7540578 prefixEnd_7540578 3871940926718903687596519 := by
  unfold tailWord_7540578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68756868518945302259567597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183351649383854139358846925 68756868518945302259567597)
  ·
    refine ⟨25783825694604488347337849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68756868518945302259567597 25783825694604488347337849)
    ·
      refine ⟨19337869270953366260503387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25783825694604488347337849 19337869270953366260503387)
      ·
        refine ⟨29006803906430049390755081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19337869270953366260503387 29006803906430049390755081)
        ·
          refine ⟨21755102929822537043066311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29006803906430049390755081 21755102929822537043066311)
          ·
            refine ⟨32632654394733805564599467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21755102929822537043066311 32632654394733805564599467)
            ·
              refine ⟨48948981592100708346899201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32632654394733805564599467 48948981592100708346899201)
              ·
                refine ⟨36711736194075531260174401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48948981592100708346899201 36711736194075531260174401)
                ·
                  refine ⟨27533802145556648445130801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36711736194075531260174401 27533802145556648445130801)
                  ·
                    refine ⟨20650351609167486333848101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27533802145556648445130801 20650351609167486333848101)
                    ·
                      refine ⟨3871940926718903687596519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20650351609167486333848101 3871940926718903687596519)
                      ·
                        rfl

theorem cell23_7540578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7540578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540578 prefixEnd_7540578 := by exact prefixLift 7540578
  have htrace : WordTrace (prefixWord ++ tailWord_7540578) baseStart_7540578 baseEnd_7540578 := by
    simpa [prefixWord, tailWord_7540578, baseEnd_7540578] using wordTrace_append hprefix tailTrace_7540578
  have hstable : (prefixWord ++ tailWord_7540578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540578).length < 2 ^ (prefixWord ++ tailWord_7540578).sum := by decide
  have hdescent : baseEnd_7540578 < baseStart_7540578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540588 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 5]
def baseStart_7540588 : Nat := 118140960795 + 7540588 * 2 ^ 59
def prefixEnd_7540588 : Nat := 4983230072969 + 3 ^ 40 * 7540588 * 2
def baseEnd_7540588 : Nat := 430216229058383183163497

theorem tailTrace_7540588 : CollatzResearch.WordTrace tailWord_7540588 prefixEnd_7540588 430216229058383183163497 := by
  unfold tailWord_7540588
  simp only [CollatzResearch.WordTrace]
  refine ⟨137513919402872490373067209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183351892537163320497422945 137513919402872490373067209)
  ·
    refine ⟨103135439552154367779800407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137513919402872490373067209 103135439552154367779800407)
    ·
      refine ⟨154703159328231551669700611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103135439552154367779800407 154703159328231551669700611)
      ·
        refine ⟨232054738992347327504550917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154703159328231551669700611 232054738992347327504550917)
        ·
          refine ⟨43510263561065123907103297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232054738992347327504550917 43510263561065123907103297)
          ·
            refine ⟨32632697670798842930327473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43510263561065123907103297 32632697670798842930327473)
            ·
              refine ⟨24474523253099132197745605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32632697670798842930327473 24474523253099132197745605)
              ·
                refine ⟨4588973109956087287077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24474523253099132197745605 4588973109956087287077301)
                ·
                  refine ⟨430216229058383183163497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4588973109956087287077301 430216229058383183163497)
                  ·
                    rfl

theorem cell23_7540588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_7540588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540588 prefixEnd_7540588 := by exact prefixLift 7540588
  have htrace : WordTrace (prefixWord ++ tailWord_7540588) baseStart_7540588 baseEnd_7540588 := by
    simpa [prefixWord, tailWord_7540588, baseEnd_7540588] using wordTrace_append hprefix tailTrace_7540588
  have hstable : (prefixWord ++ tailWord_7540588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540588).length < 2 ^ (prefixWord ++ tailWord_7540588).sum := by decide
  have hdescent : baseEnd_7540588 < baseStart_7540588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540728 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_7540728 : Nat := 118140960795 + 7540728 * 2 ^ 59
def prefixEnd_7540728 : Nat := 4983230072969 + 3 ^ 40 * 7540728 * 2
def baseEnd_7540728 : Nat := 3872017948817078100720829

theorem tailTrace_7540728 : CollatzResearch.WordTrace tailWord_7540728 prefixEnd_7540728 3872017948817078100720829 := by
  unfold tailWord_7540728
  simp only [CollatzResearch.WordTrace]
  refine ⟨137516472512618892328115419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183355296683491856437487225 137516472512618892328115419)
  ·
    refine ⟨206274708768928338492173129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137516472512618892328115419 206274708768928338492173129)
    ·
      refine ⟨154706031576696253869129847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206274708768928338492173129 154706031576696253869129847)
      ·
        refine ⟨232059047365044380803694771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154706031576696253869129847 232059047365044380803694771)
        ·
          refine ⟨348088571047566571205542157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232059047365044380803694771 348088571047566571205542157)
          ·
            refine ⟨130533214142837464202078309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348088571047566571205542157 130533214142837464202078309)
            ·
              refine ⟨24474977651782024537889683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130533214142837464202078309 24474977651782024537889683)
              ·
                refine ⟨36712466477673036806834525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24474977651782024537889683 36712466477673036806834525)
                ·
                  refine ⟨13767174929127388802562947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36712466477673036806834525 13767174929127388802562947)
                  ·
                    refine ⟨20650762393691083203844421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13767174929127388802562947 20650762393691083203844421)
                    ·
                      refine ⟨3872017948817078100720829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20650762393691083203844421 3872017948817078100720829)
                      ·
                        rfl

theorem cell23_7540728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_7540728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540728 prefixEnd_7540728 := by exact prefixLift 7540728
  have htrace : WordTrace (prefixWord ++ tailWord_7540728) baseStart_7540728 baseEnd_7540728 := by
    simpa [prefixWord, tailWord_7540728, baseEnd_7540728] using wordTrace_append hprefix tailTrace_7540728
  have hstable : (prefixWord ++ tailWord_7540728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540728).length < 2 ^ (prefixWord ++ tailWord_7540728).sum := by decide
  have hdescent : baseEnd_7540728 < baseStart_7540728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540748 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7540748 : Nat := 118140960795 + 7540748 * 2 ^ 59
def prefixEnd_7540748 : Nat := 4983230072969 + 3 ^ 40 * 7540748 * 2
def baseEnd_7540748 : Nat := 3872028218430168022470737

theorem tailTrace_7540748 : CollatzResearch.WordTrace tailWord_7540748 prefixEnd_7540748 3872028218430168022470737 := by
  unfold tailWord_7540748
  simp only [CollatzResearch.WordTrace]
  refine ⟨137516837242582664035979449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183355782990110218714639265 137516837242582664035979449)
  ·
    refine ⟨103137627931936998026984587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137516837242582664035979449 103137627931936998026984587)
    ·
      refine ⟨154706441897905497040476881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103137627931936998026984587 154706441897905497040476881)
      ·
        refine ⟨116029831423429122780357661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154706441897905497040476881 116029831423429122780357661)
        ·
          refine ⟨43511186783785921042634123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116029831423429122780357661 43511186783785921042634123)
          ·
            refine ⟨65266780175678881563951185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43511186783785921042634123 65266780175678881563951185)
            ·
              refine ⟨48950085131759161172963389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65266780175678881563951185 48950085131759161172963389)
              ·
                refine ⟨18356281924409685439861271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48950085131759161172963389 18356281924409685439861271)
                ·
                  refine ⟨27534422886614528159791907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18356281924409685439861271 27534422886614528159791907)
                  ·
                    refine ⟨41301634329921792239687861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27534422886614528159791907 41301634329921792239687861)
                    ·
                      refine ⟨3872028218430168022470737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41301634329921792239687861 3872028218430168022470737)
                      ·
                        rfl

theorem cell23_7540748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7540748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540748 prefixEnd_7540748 := by exact prefixLift 7540748
  have htrace : WordTrace (prefixWord ++ tailWord_7540748) baseStart_7540748 baseEnd_7540748 := by
    simpa [prefixWord, tailWord_7540748, baseEnd_7540748] using wordTrace_append hprefix tailTrace_7540748
  have hstable : (prefixWord ++ tailWord_7540748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540748).length < 2 ^ (prefixWord ++ tailWord_7540748).sum := by decide
  have hdescent : baseEnd_7540748 < baseStart_7540748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540755 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 2, 4]
def baseStart_7540755 : Nat := 118140960795 + 7540755 * 2 ^ 59
def prefixEnd_7540755 : Nat := 4983230072969 + 3 ^ 40 * 7540755 * 2
def baseEnd_7540755 : Nat := 1290677270931583165027735

theorem tailTrace_7540755 : CollatzResearch.WordTrace tailWord_7540755 prefixEnd_7540755 1290677270931583165027735 := by
  unfold tailWord_7540755
  simp only [CollatzResearch.WordTrace]
  refine ⟨275033929796139968267463719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183355953197426645511642479 275033929796139968267463719)
  ·
    refine ⟨412550894694209952401195579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275033929796139968267463719 412550894694209952401195579)
    ·
      refine ⟨618826342041314928601793369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412550894694209952401195579 618826342041314928601793369)
      ·
        refine ⟨464119756530986196451345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 618826342041314928601793369 464119756530986196451345027)
        ·
          refine ⟨696179634796479294677017541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464119756530986196451345027 696179634796479294677017541)
          ·
            refine ⟨130533681524339867751940789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 696179634796479294677017541 130533681524339867751940789)
            ·
              refine ⟨12237532642906862601744449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130533681524339867751940789 12237532642906862601744449)
              ·
                refine ⟨9178149482180146951308337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12237532642906862601744449 9178149482180146951308337)
                ·
                  refine ⟨6883612111635110213481253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178149482180146951308337 6883612111635110213481253)
                  ·
                    refine ⟨1290677270931583165027735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883612111635110213481253 1290677270931583165027735)
                    ·
                      rfl

theorem cell23_7540755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 4].length) (baseStart_7540755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540755 prefixEnd_7540755 := by exact prefixLift 7540755
  have htrace : WordTrace (prefixWord ++ tailWord_7540755) baseStart_7540755 baseEnd_7540755 := by
    simpa [prefixWord, tailWord_7540755, baseEnd_7540755] using wordTrace_append hprefix tailTrace_7540755
  have hstable : (prefixWord ++ tailWord_7540755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540755).length < 2 ^ (prefixWord ++ tailWord_7540755).sum := by decide
  have hdescent : baseEnd_7540755 < baseStart_7540755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540756 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7540756 : Nat := 118140960795 + 7540756 * 2 ^ 59
def prefixEnd_7540756 : Nat := 4983230072969 + 3 ^ 40 * 7540756 * 2
def baseEnd_7540756 : Nat := 3872032326275403991170701

theorem tailTrace_7540756 : CollatzResearch.WordTrace tailWord_7540756 prefixEnd_7540756 3872032326275403991170701 := by
  unfold tailWord_7540756
  simp only [CollatzResearch.WordTrace]
  refine ⟨137516983134568172719125061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183355977512757563625500081 137516983134568172719125061)
  ·
    refine ⟨25784434337731532384835949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137516983134568172719125061 25784434337731532384835949)
    ·
      refine ⟨9669162876649324644313481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25784434337731532384835949 9669162876649324644313481)
      ·
        refine ⟨7251872157486993483235111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9669162876649324644313481 7251872157486993483235111)
        ·
          refine ⟨10877808236230490224852667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251872157486993483235111 10877808236230490224852667)
          ·
            refine ⟨16316712354345735337279001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10877808236230490224852667 16316712354345735337279001)
            ·
              refine ⟨12237534265759301502959251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16316712354345735337279001 12237534265759301502959251)
              ·
                refine ⟨18356301398638952254438877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12237534265759301502959251 18356301398638952254438877)
                ·
                  refine ⟨6883613024489607095414579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18356301398638952254438877 6883613024489607095414579)
                  ·
                    refine ⟨10325419536734410643121869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6883613024489607095414579 10325419536734410643121869)
                    ·
                      refine ⟨3872032326275403991170701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10325419536734410643121869 3872032326275403991170701)
                      ·
                        rfl

theorem cell23_7540756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7540756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540756 prefixEnd_7540756 := by exact prefixLift 7540756
  have htrace : WordTrace (prefixWord ++ tailWord_7540756) baseStart_7540756 baseEnd_7540756 := by
    simpa [prefixWord, tailWord_7540756, baseEnd_7540756] using wordTrace_append hprefix tailTrace_7540756
  have hstable : (prefixWord ++ tailWord_7540756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540756).length < 2 ^ (prefixWord ++ tailWord_7540756).sum := by decide
  have hdescent : baseEnd_7540756 < baseStart_7540756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540761 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_7540761 : Nat := 118140960795 + 7540761 * 2 ^ 59
def prefixEnd_7540761 : Nat := 4983230072969 + 3 ^ 40 * 7540761 * 2
def baseEnd_7540761 : Nat := 3872034893678676471608177

theorem tailTrace_7540761 : CollatzResearch.WordTrace tailWord_7540761 prefixEnd_7540761 3872034893678676471608177 := by
  unfold tailWord_7540761
  simp only [CollatzResearch.WordTrace]
  refine ⟨275034148634118231292182137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183356099089412154194788091 275034148634118231292182137)
  ·
    refine ⟨206275611475588673469136603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275034148634118231292182137 206275611475588673469136603)
    ·
      refine ⟨309413417213383010203704905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206275611475588673469136603 309413417213383010203704905)
      ·
        refine ⟨232060062910037257652778679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309413417213383010203704905 232060062910037257652778679)
        ·
          refine ⟨348090094365055886479168019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232060062910037257652778679 348090094365055886479168019)
          ·
            refine ⟨522135141547583829718752029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348090094365055886479168019 522135141547583829718752029)
            ·
              refine ⟨195800678080343936144532011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522135141547583829718752029 195800678080343936144532011)
              ·
                refine ⟨293701017120515904216798017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195800678080343936144532011 293701017120515904216798017)
                ·
                  refine ⟨220275762840386928162598513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 293701017120515904216798017 220275762840386928162598513)
                  ·
                    refine ⟨165206822130290196121948885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220275762840386928162598513 165206822130290196121948885)
                    ·
                      refine ⟨3872034893678676471608177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165206822130290196121948885 3872034893678676471608177)
                      ·
                        rfl

theorem cell23_7540761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_7540761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540761 prefixEnd_7540761 := by exact prefixLift 7540761
  have htrace : WordTrace (prefixWord ++ tailWord_7540761) baseStart_7540761 baseEnd_7540761 := by
    simpa [prefixWord, tailWord_7540761, baseEnd_7540761] using wordTrace_append hprefix tailTrace_7540761
  have hstable : (prefixWord ++ tailWord_7540761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540761).length < 2 ^ (prefixWord ++ tailWord_7540761).sum := by decide
  have hdescent : baseEnd_7540761 < baseStart_7540761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540762 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2]
def baseStart_7540762 : Nat := 118140960795 + 7540762 * 2 ^ 59
def prefixEnd_7540762 : Nat := 4983230072969 + 3 ^ 40 * 7540762 * 2
def baseEnd_7540762 : Nat := 3872035407159330967695673

theorem tailTrace_7540762 : CollatzResearch.WordTrace tailWord_7540762 prefixEnd_7540762 3872035407159330967695673 := by
  unfold tailWord_7540762
  simp only [CollatzResearch.WordTrace]
  refine ⟨68758546276778652115742135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183356123404743072308645693 68758546276778652115742135)
  ·
    refine ⟨103137819415167978173613203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68758546276778652115742135 103137819415167978173613203)
    ·
      refine ⟨154706729122751967260419805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103137819415167978173613203 154706729122751967260419805)
      ·
        refine ⟨58015023421031987722657427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154706729122751967260419805 58015023421031987722657427)
        ·
          refine ⟨87022535131547981583986141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58015023421031987722657427 87022535131547981583986141)
          ·
            refine ⟨32633450674330493093994803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87022535131547981583986141 32633450674330493093994803)
            ·
              refine ⟨48950176011495739640992205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32633450674330493093994803 48950176011495739640992205)
              ·
                refine ⟨18356316004310902365372077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48950176011495739640992205 18356316004310902365372077)
                ·
                  refine ⟨6883618501616588387014529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18356316004310902365372077 6883618501616588387014529)
                  ·
                    refine ⟨5162713876212441290260897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6883618501616588387014529 5162713876212441290260897)
                    ·
                      refine ⟨3872035407159330967695673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162713876212441290260897 3872035407159330967695673)
                      ·
                        rfl

theorem cell23_7540762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_7540762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540762 prefixEnd_7540762 := by exact prefixLift 7540762
  have htrace : WordTrace (prefixWord ++ tailWord_7540762) baseStart_7540762 baseEnd_7540762 := by
    simpa [prefixWord, tailWord_7540762, baseEnd_7540762] using wordTrace_append hprefix tailTrace_7540762
  have hstable : (prefixWord ++ tailWord_7540762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540762).length < 2 ^ (prefixWord ++ tailWord_7540762).sum := by decide
  have hdescent : baseEnd_7540762 < baseStart_7540762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540765 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_7540765 : Nat := 118140960795 + 7540765 * 2 ^ 59
def prefixEnd_7540765 : Nat := 4983230072969 + 3 ^ 40 * 7540765 * 2
def baseEnd_7540765 : Nat := 3872036947601294455958159

theorem tailTrace_7540765 : CollatzResearch.WordTrace tailWord_7540765 prefixEnd_7540765 3872036947601294455958159 := by
  unfold tailWord_7540765
  simp only [CollatzResearch.WordTrace]
  refine ⟨275034294526103739975327749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183356196350735826650218499 275034294526103739975327749)
  ·
    refine ⟨51568930223644451245373953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275034294526103739975327749 51568930223644451245373953)
    ·
      refine ⟨38676697667733338434030465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51568930223644451245373953 38676697667733338434030465)
      ·
        refine ⟨29007523250800003825522849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38676697667733338434030465 29007523250800003825522849)
        ·
          refine ⟨21755642438100002869142137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29007523250800003825522849 21755642438100002869142137)
          ·
            refine ⟨16316731828575002151856603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21755642438100002869142137 16316731828575002151856603)
            ·
              refine ⟨24475097742862503227784905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16316731828575002151856603 24475097742862503227784905)
              ·
                refine ⟨18356323307146877420838679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24475097742862503227784905 18356323307146877420838679)
                ·
                  refine ⟨27534484960720316131258019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18356323307146877420838679 27534484960720316131258019)
                  ·
                    refine ⟨41301727441080474196887029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27534484960720316131258019 41301727441080474196887029)
                    ·
                      refine ⟨3872036947601294455958159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41301727441080474196887029 3872036947601294455958159)
                      ·
                        rfl

theorem cell23_7540765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_7540765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540765 prefixEnd_7540765 := by exact prefixLift 7540765
  have htrace : WordTrace (prefixWord ++ tailWord_7540765) baseStart_7540765 baseEnd_7540765 := by
    simpa [prefixWord, tailWord_7540765, baseEnd_7540765] using wordTrace_append hprefix tailTrace_7540765
  have hstable : (prefixWord ++ tailWord_7540765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540765).length < 2 ^ (prefixWord ++ tailWord_7540765).sum := by decide
  have hdescent : baseEnd_7540765 < baseStart_7540765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540772 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_7540772 : Nat := 118140960795 + 7540772 * 2 ^ 59
def prefixEnd_7540772 : Nat := 4983230072969 + 3 ^ 40 * 7540772 * 2
def baseEnd_7540772 : Nat := 1290680180655291976190209

theorem tailTrace_7540772 : CollatzResearch.WordTrace tailWord_7540772 prefixEnd_7540772 1290680180655291976190209 := by
  unfold tailWord_7540772
  simp only [CollatzResearch.WordTrace]
  refine ⟨137517274918539190085416285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183356366558052253447221713 137517274918539190085416285)
  ·
    refine ⟨51568978094452196282031107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137517274918539190085416285 51568978094452196282031107)
    ·
      refine ⟨77353467141678294423046661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51568978094452196282031107 77353467141678294423046661)
      ·
        refine ⟨14503775089064680204321249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77353467141678294423046661 14503775089064680204321249)
        ·
          refine ⟨10877831316798510153240937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14503775089064680204321249 10877831316798510153240937)
          ·
            refine ⟨8158373487598882614930703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10877831316798510153240937 8158373487598882614930703)
            ·
              refine ⟨12237560231398323922396055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158373487598882614930703 12237560231398323922396055)
              ·
                refine ⟨18356340347097485883594083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12237560231398323922396055 18356340347097485883594083)
                ·
                  refine ⟨27534510520646228825391125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18356340347097485883594083 27534510520646228825391125)
                  ·
                    refine ⟨1290680180655291976190209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27534510520646228825391125 1290680180655291976190209)
                    ·
                      rfl

theorem cell23_7540772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_7540772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540772 prefixEnd_7540772 := by exact prefixLift 7540772
  have htrace : WordTrace (prefixWord ++ tailWord_7540772) baseStart_7540772 baseEnd_7540772 := by
    simpa [prefixWord, tailWord_7540772, baseEnd_7540772] using wordTrace_append hprefix tailTrace_7540772
  have hstable : (prefixWord ++ tailWord_7540772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540772).length < 2 ^ (prefixWord ++ tailWord_7540772).sum := by decide
  have hdescent : baseEnd_7540772 < baseStart_7540772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540782 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7540782 : Nat := 118140960795 + 7540782 * 2 ^ 59
def prefixEnd_7540782 : Nat := 4983230072969 + 3 ^ 40 * 7540782 * 2
def baseEnd_7540782 : Nat := 3872045676772420889445581

theorem tailTrace_7540782 : CollatzResearch.WordTrace tailWord_7540782 prefixEnd_7540782 3872045676772420889445581 := by
  unfold tailWord_7540782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34379364320880268984837075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183356609711361434585797733 34379364320880268984837075)
  ·
    refine ⟨51569046481320403477255613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34379364320880268984837075 51569046481320403477255613)
    ·
      refine ⟨19338392430495151303970855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51569046481320403477255613 19338392430495151303970855)
      ·
        refine ⟨29007588645742726955956283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19338392430495151303970855 29007588645742726955956283)
        ·
          refine ⟨43511382968614090433934425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29007588645742726955956283 43511382968614090433934425)
          ·
            refine ⟨32633537226460567825450819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43511382968614090433934425 32633537226460567825450819)
            ·
              refine ⟨48950305839690851738176229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32633537226460567825450819 48950305839690851738176229)
              ·
                refine ⟨9178182344942034700908043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48950305839690851738176229 9178182344942034700908043)
                ·
                  refine ⟨13767273517413052051362065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9178182344942034700908043 13767273517413052051362065)
                  ·
                    refine ⟨10325455138059789038521549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13767273517413052051362065 10325455138059789038521549)
                    ·
                      refine ⟨3872045676772420889445581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10325455138059789038521549 3872045676772420889445581)
                      ·
                        rfl

theorem cell23_7540782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7540782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540782 prefixEnd_7540782 := by exact prefixLift 7540782
  have htrace : WordTrace (prefixWord ++ tailWord_7540782) baseStart_7540782 baseEnd_7540782 := by
    simpa [prefixWord, tailWord_7540782, baseEnd_7540782] using wordTrace_append hprefix tailTrace_7540782
  have hstable : (prefixWord ++ tailWord_7540782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540782).length < 2 ^ (prefixWord ++ tailWord_7540782).sum := by decide
  have hdescent : baseEnd_7540782 < baseStart_7540782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540785 : List Nat := [1, 2, 2, 3, 1, 5, 2, 7]
def baseStart_7540785 : Nat := 118140960795 + 7540785 * 2 ^ 59
def prefixEnd_7540785 : Nat := 4983230072969 + 3 ^ 40 * 7540785 * 2
def baseEnd_7540785 : Nat := 143409156193125347322521

theorem tailTrace_7540785 : CollatzResearch.WordTrace tailWord_7540785 prefixEnd_7540785 143409156193125347322521 := by
  unfold tailWord_7540785
  simp only [CollatzResearch.WordTrace]
  refine ⟨275035023986031283391055809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183356682657354188927370539 275035023986031283391055809)
  ·
    refine ⟨206276267989523462543291857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275035023986031283391055809 206276267989523462543291857)
    ·
      refine ⟨154707200992142596907468893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206276267989523462543291857 154707200992142596907468893)
      ·
        refine ⟨58015200372053473840300835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154707200992142596907468893 58015200372053473840300835)
        ·
          refine ⟨87022800558080210760451253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58015200372053473840300835 87022800558080210760451253)
          ·
            refine ⟨8158387552320019758792305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87022800558080210760451253 8158387552320019758792305)
            ·
              refine ⟨6118790664240014819094229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158387552320019758792305 6118790664240014819094229)
              ·
                refine ⟨143409156193125347322521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6118790664240014819094229 143409156193125347322521)
                ·
                  rfl

theorem cell23_7540785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 7].length) (baseStart_7540785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540785 prefixEnd_7540785 := by exact prefixLift 7540785
  have htrace : WordTrace (prefixWord ++ tailWord_7540785) baseStart_7540785 baseEnd_7540785 := by
    simpa [prefixWord, tailWord_7540785, baseEnd_7540785] using wordTrace_append hprefix tailTrace_7540785
  have hstable : (prefixWord ++ tailWord_7540785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540785).length < 2 ^ (prefixWord ++ tailWord_7540785).sum := by decide
  have hdescent : baseEnd_7540785 < baseStart_7540785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540805 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_7540805 : Nat := 118140960795 + 7540805 * 2 ^ 59
def prefixEnd_7540805 : Nat := 4983230072969 + 3 ^ 40 * 7540805 * 2
def baseEnd_7540805 : Nat := 3872057486827474299457975

theorem tailTrace_7540805 : CollatzResearch.WordTrace tailWord_7540805 prefixEnd_7540805 3872057486827474299457975 := by
  unfold tailWord_7540805
  simp only [CollatzResearch.WordTrace]
  refine ⟨275035753445958826806783869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183357168963972551204522579 275035753445958826806783869)
  ·
    refine ⟨103138407542234560052543951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275035753445958826806783869 103138407542234560052543951)
    ·
      refine ⟨154707611313351840078815927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103138407542234560052543951 154707611313351840078815927)
      ·
        refine ⟨232061416970027760118223891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154707611313351840078815927 232061416970027760118223891)
        ·
          refine ⟨348092125455041640177335837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232061416970027760118223891 348092125455041640177335837)
          ·
            refine ⟨130534547045640615066500939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348092125455041640177335837 130534547045640615066500939)
            ·
              refine ⟨195801820568460922599751409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130534547045640615066500939 195801820568460922599751409)
              ·
                refine ⟨146851365426345691949813557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195801820568460922599751409 146851365426345691949813557)
                ·
                  refine ⟨13767315508719908620295021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146851365426345691949813557 13767315508719908620295021)
                  ·
                    refine ⟨5162743315769965732610633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13767315508719908620295021 5162743315769965732610633)
                    ·
                      refine ⟨3872057486827474299457975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162743315769965732610633 3872057486827474299457975)
                      ·
                        rfl

theorem cell23_7540805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_7540805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540805 prefixEnd_7540805 := by exact prefixLift 7540805
  have htrace : WordTrace (prefixWord ++ tailWord_7540805) baseStart_7540805 baseEnd_7540805 := by
    simpa [prefixWord, tailWord_7540805, baseEnd_7540805] using wordTrace_append hprefix tailTrace_7540805
  have hstable : (prefixWord ++ tailWord_7540805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540805).length < 2 ^ (prefixWord ++ tailWord_7540805).sum := by decide
  have hdescent : baseEnd_7540805 < baseStart_7540805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540813 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_7540813 : Nat := 118140960795 + 7540813 * 2 ^ 59
def prefixEnd_7540813 : Nat := 4983230072969 + 3 ^ 40 * 7540813 * 2
def baseEnd_7540813 : Nat := 3872061594672710268157939

theorem tailTrace_7540813 : CollatzResearch.WordTrace tailWord_7540813 prefixEnd_7540813 3872061594672710268157939 := by
  unfold tailWord_7540813
  simp only [CollatzResearch.WordTrace]
  refine ⟨275036045229929844173075093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183357363486619896115383395 275036045229929844173075093)
  ·
    refine ⟨12892314620152961445612895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275036045229929844173075093 12892314620152961445612895)
    ·
      refine ⟨19338471930229442168419343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892314620152961445612895 19338471930229442168419343)
      ·
        refine ⟨29007707895344163252629015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19338471930229442168419343 29007707895344163252629015)
        ·
          refine ⟨43511561843016244878943523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29007707895344163252629015 43511561843016244878943523)
          ·
            refine ⟨65267342764524367318415285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43511561843016244878943523 65267342764524367318415285)
            ·
              refine ⟨6118813384174159436101433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65267342764524367318415285 6118813384174159436101433)
              ·
                refine ⟨4589110038130619577076075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118813384174159436101433 4589110038130619577076075)
                ·
                  refine ⟨6883665057195929365614113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589110038130619577076075 6883665057195929365614113)
                  ·
                    refine ⟨5162748792896947024210585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6883665057195929365614113 5162748792896947024210585)
                    ·
                      refine ⟨3872061594672710268157939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162748792896947024210585 3872061594672710268157939)
                      ·
                        rfl

theorem cell23_7540813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_7540813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540813 prefixEnd_7540813 := by exact prefixLift 7540813
  have htrace : WordTrace (prefixWord ++ tailWord_7540813) baseStart_7540813 baseEnd_7540813 := by
    simpa [prefixWord, tailWord_7540813, baseEnd_7540813] using wordTrace_append hprefix tailTrace_7540813
  have hstable : (prefixWord ++ tailWord_7540813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540813).length < 2 ^ (prefixWord ++ tailWord_7540813).sum := by decide
  have hdescent : baseEnd_7540813 < baseStart_7540813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540869 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_7540869 : Nat := 118140960795 + 7540869 * 2 ^ 59
def prefixEnd_7540869 : Nat := 4983230072969 + 3 ^ 40 * 7540869 * 2
def baseEnd_7540869 : Nat := 3872090349589362049057681

theorem tailTrace_7540869 : CollatzResearch.WordTrace tailWord_7540869 prefixEnd_7540869 3872090349589362049057681 := by
  unfold tailWord_7540869
  simp only [CollatzResearch.WordTrace]
  refine ⟨275038087717726965737113661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183358725145151310491409107 275038087717726965737113661)
  ·
    refine ⟨103139282894147612151417623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275038087717726965737113661 103139282894147612151417623)
    ·
      refine ⟨154708924341221418227126435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103139282894147612151417623 154708924341221418227126435)
      ·
        refine ⟨232063386511832127340689653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154708924341221418227126435 232063386511832127340689653)
        ·
          refine ⟨21755942485484261938189655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232063386511832127340689653 21755942485484261938189655)
          ·
            refine ⟨32633913728226392907284483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21755942485484261938189655 32633913728226392907284483)
            ·
              refine ⟨48950870592339589360926725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32633913728226392907284483 48950870592339589360926725)
              ·
                refine ⟨9178288236063673005173761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48950870592339589360926725 9178288236063673005173761)
                ·
                  refine ⟨6883716177047754753880321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178288236063673005173761 6883716177047754753880321)
                  ·
                    refine ⟨5162787132785816065410241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6883716177047754753880321 5162787132785816065410241)
                    ·
                      refine ⟨3872090349589362049057681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162787132785816065410241 3872090349589362049057681)
                      ·
                        rfl

theorem cell23_7540869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_7540869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540869 prefixEnd_7540869 := by exact prefixLift 7540869
  have htrace : WordTrace (prefixWord ++ tailWord_7540869) baseStart_7540869 baseEnd_7540869 := by
    simpa [prefixWord, tailWord_7540869, baseEnd_7540869] using wordTrace_append hprefix tailTrace_7540869
  have hstable : (prefixWord ++ tailWord_7540869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540869).length < 2 ^ (prefixWord ++ tailWord_7540869).sum := by decide
  have hdescent : baseEnd_7540869 < baseStart_7540869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540885 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_7540885 : Nat := 118140960795 + 7540885 * 2 ^ 59
def prefixEnd_7540885 : Nat := 4983230072969 + 3 ^ 40 * 7540885 * 2
def baseEnd_7540885 : Nat := 3872098565279833986457607

theorem tailTrace_7540885 : CollatzResearch.WordTrace tailWord_7540885 prefixEnd_7540885 3872098565279833986457607 := by
  unfold tailWord_7540885
  simp only [CollatzResearch.WordTrace]
  refine ⟨275038671285669000469696109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183359114190446000313130739 275038671285669000469696109)
  ·
    refine ⟨103139501732125875176136041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275038671285669000469696109 103139501732125875176136041)
    ·
      refine ⟨77354626299094406382102031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103139501732125875176136041 77354626299094406382102031)
      ·
        refine ⟨116031939448641609573153047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77354626299094406382102031 116031939448641609573153047)
        ·
          refine ⟨174047909172962414359729571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116031939448641609573153047 174047909172962414359729571)
          ·
            refine ⟨261071863759443621539594357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174047909172962414359729571 261071863759443621539594357)
            ·
              refine ⟨24475487227447839519336971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261071863759443621539594357 24475487227447839519336971)
              ·
                refine ⟨36713230841171759279005457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24475487227447839519336971 36713230841171759279005457)
                ·
                  refine ⟨27534923130878819459254093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36713230841171759279005457 27534923130878819459254093)
                  ·
                    refine ⟨10325596174079557297220285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27534923130878819459254093 10325596174079557297220285)
                    ·
                      refine ⟨3872098565279833986457607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10325596174079557297220285 3872098565279833986457607)
                      ·
                        rfl

theorem cell23_7540885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_7540885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540885 prefixEnd_7540885 := by exact prefixLift 7540885
  have htrace : WordTrace (prefixWord ++ tailWord_7540885) baseStart_7540885 baseEnd_7540885 := by
    simpa [prefixWord, tailWord_7540885, baseEnd_7540885] using wordTrace_append hprefix tailTrace_7540885
  have hstable : (prefixWord ++ tailWord_7540885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540885).length < 2 ^ (prefixWord ++ tailWord_7540885).sum := by decide
  have hdescent : baseEnd_7540885 < baseStart_7540885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540909 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 5]
def baseStart_7540909 : Nat := 118140960795 + 7540909 * 2 ^ 59
def prefixEnd_7540909 : Nat := 4983230072969 + 3 ^ 40 * 7540909 * 2
def baseEnd_7540909 : Nat := 430234543201726876950833

theorem tailTrace_7540909 : CollatzResearch.WordTrace tailWord_7540909 prefixEnd_7540909 430234543201726876950833 := by
  unfold tailWord_7540909
  simp only [CollatzResearch.WordTrace]
  refine ⟨275039546637582052568569781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183359697758388035045713187 275039546637582052568569781)
  ·
    refine ⟨25784957497273317428303417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275039546637582052568569781 25784957497273317428303417)
    ·
      refine ⟨19338718122954988071227563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25784957497273317428303417 19338718122954988071227563)
      ·
        refine ⟨29008077184432482106841345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19338718122954988071227563 29008077184432482106841345)
        ·
          refine ⟨21756057888324361580131009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29008077184432482106841345 21756057888324361580131009)
          ·
            refine ⟨16317043416243271185098257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21756057888324361580131009 16317043416243271185098257)
            ·
              refine ⟨12237782562182453388823693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16317043416243271185098257 12237782562182453388823693)
              ·
                refine ⟨4589168460818420020808885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12237782562182453388823693 4589168460818420020808885)
                ·
                  refine ⟨430234543201726876950833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4589168460818420020808885 430234543201726876950833)
                  ·
                    rfl

theorem cell23_7540909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_7540909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540909 prefixEnd_7540909 := by exact prefixLift 7540909
  have htrace : WordTrace (prefixWord ++ tailWord_7540909) baseStart_7540909 baseEnd_7540909 := by
    simpa [prefixWord, tailWord_7540909, baseEnd_7540909] using wordTrace_append hprefix tailTrace_7540909
  have hstable : (prefixWord ++ tailWord_7540909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540909).length < 2 ^ (prefixWord ++ tailWord_7540909).sum := by decide
  have hdescent : baseEnd_7540909 < baseStart_7540909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540925 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7540925 : Nat := 118140960795 + 7540925 * 2 ^ 59
def prefixEnd_7540925 : Nat := 4983230072969 + 3 ^ 40 * 7540925 * 2
def baseEnd_7540925 : Nat := 3872119104506013829957423

theorem tailTrace_7540925 : CollatzResearch.WordTrace tailWord_7540925 prefixEnd_7540925 3872119104506013829957423 := by
  unfold tailWord_7540925
  simp only [CollatzResearch.WordTrace]
  refine ⟨275040130205524087301152229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183360086803682724867434819 275040130205524087301152229)
  ·
    refine ⟨51570024413535766368966043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275040130205524087301152229 51570024413535766368966043)
    ·
      refine ⟨77355036620303649553449065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51570024413535766368966043 77355036620303649553449065)
      ·
        refine ⟨58016277465227737165086799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77355036620303649553449065 58016277465227737165086799)
        ·
          refine ⟨87024416197841605747630199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58016277465227737165086799 87024416197841605747630199)
          ·
            refine ⟨130536624296762408621445299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87024416197841605747630199 130536624296762408621445299)
            ·
              refine ⟨195804936445143612932167949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130536624296762408621445299 195804936445143612932167949)
              ·
                refine ⟨73426851166928854849562981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195804936445143612932167949 73426851166928854849562981)
                ·
                  refine ⟨13767534593799160284293059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73426851166928854849562981 13767534593799160284293059)
                  ·
                    refine ⟨20651301890698740426439589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13767534593799160284293059 20651301890698740426439589)
                    ·
                      refine ⟨3872119104506013829957423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20651301890698740426439589 3872119104506013829957423)
                      ·
                        rfl

theorem cell23_7540925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7540925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540925 prefixEnd_7540925 := by exact prefixLift 7540925
  have htrace : WordTrace (prefixWord ++ tailWord_7540925) baseStart_7540925 baseEnd_7540925 := by
    simpa [prefixWord, tailWord_7540925, baseEnd_7540925] using wordTrace_append hprefix tailTrace_7540925
  have hstable : (prefixWord ++ tailWord_7540925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540925).length < 2 ^ (prefixWord ++ tailWord_7540925).sum := by decide
  have hdescent : baseEnd_7540925 < baseStart_7540925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540945 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_7540945 : Nat := 118140960795 + 7540945 * 2 ^ 59
def prefixEnd_7540945 : Nat := 4983230072969 + 3 ^ 40 * 7540945 * 2
def baseEnd_7540945 : Nat := 3872129374119103751707331

theorem tailTrace_7540945 : CollatzResearch.WordTrace tailWord_7540945 prefixEnd_7540945 3872129374119103751707331 := by
  unfold tailWord_7540945
  simp only [CollatzResearch.WordTrace]
  refine ⟨275040859665451630716880289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183360573110301087144586859 275040859665451630716880289)
  ·
    refine ⟨206280644749088723037660217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275040859665451630716880289 206280644749088723037660217)
    ·
      refine ⟨154710483561816542278245163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206280644749088723037660217 154710483561816542278245163)
      ·
        refine ⟨232065725342724813417367745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154710483561816542278245163 232065725342724813417367745)
        ·
          refine ⟨174049294007043610063025809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232065725342724813417367745 174049294007043610063025809)
          ·
            refine ⟨130536970505282707547269357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174049294007043610063025809 130536970505282707547269357)
            ·
              refine ⟨48951363939481015330226009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130536970505282707547269357 48951363939481015330226009)
              ·
                refine ⟨36713522954610761497669507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48951363939481015330226009 36713522954610761497669507)
                ·
                  refine ⟨55070284431916142246504261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36713522954610761497669507 55070284431916142246504261)
                  ·
                    refine ⟨10325678330984276671219549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55070284431916142246504261 10325678330984276671219549)
                    ·
                      refine ⟨3872129374119103751707331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10325678330984276671219549 3872129374119103751707331)
                      ·
                        rfl

theorem cell23_7540945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_7540945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540945 prefixEnd_7540945 := by exact prefixLift 7540945
  have htrace : WordTrace (prefixWord ++ tailWord_7540945) baseStart_7540945 baseEnd_7540945 := by
    simpa [prefixWord, tailWord_7540945, baseEnd_7540945] using wordTrace_append hprefix tailTrace_7540945
  have hstable : (prefixWord ++ tailWord_7540945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540945).length < 2 ^ (prefixWord ++ tailWord_7540945).sum := by decide
  have hdescent : baseEnd_7540945 < baseStart_7540945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540952 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_7540952 : Nat := 118140960795 + 7540952 * 2 ^ 59
def prefixEnd_7540952 : Nat := 4983230072969 + 3 ^ 40 * 7540952 * 2
def baseEnd_7540952 : Nat := 1290710989494561741439933

theorem tailTrace_7540952 : CollatzResearch.WordTrace tailWord_7540952 prefixEnd_7540952 1290710989494561741439933 := by
  unfold tailWord_7540952
  simp only [CollatzResearch.WordTrace]
  refine ⟨137520557488213135456192555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183360743317617513941590073 137520557488213135456192555)
  ·
    refine ⟨206280836232319703184288833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137520557488213135456192555 206280836232319703184288833)
    ·
      refine ⟨154710627174239777388216625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206280836232319703184288833 154710627174239777388216625)
      ·
        refine ⟨116032970380679833041162469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154710627174239777388216625 116032970380679833041162469)
        ·
          refine ⟨21756181946377468695217963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116032970380679833041162469 21756181946377468695217963)
          ·
            refine ⟨32634272919566203042826945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21756181946377468695217963 32634272919566203042826945)
            ·
              refine ⟨24475704689674652282120209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32634272919566203042826945 24475704689674652282120209)
              ·
                refine ⟨18356778517255989211590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24475704689674652282120209 18356778517255989211590157)
                ·
                  refine ⟨6883791943970995954346309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18356778517255989211590157 6883791943970995954346309)
                  ·
                    refine ⟨1290710989494561741439933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883791943970995954346309 1290710989494561741439933)
                    ·
                      rfl

theorem cell23_7540952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_7540952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540952 prefixEnd_7540952 := by exact prefixLift 7540952
  have htrace : WordTrace (prefixWord ++ tailWord_7540952) baseStart_7540952 baseEnd_7540952 := by
    simpa [prefixWord, tailWord_7540952, baseEnd_7540952] using wordTrace_append hprefix tailTrace_7540952
  have hstable : (prefixWord ++ tailWord_7540952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540952).length < 2 ^ (prefixWord ++ tailWord_7540952).sum := by decide
  have hdescent : baseEnd_7540952 < baseStart_7540952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540965 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 8]
def baseStart_7540965 : Nat := 118140960795 + 7540965 * 2 ^ 59
def prefixEnd_7540965 : Nat := 4983230072969 + 3 ^ 40 * 7540965 * 2
def baseEnd_7540965 : Nat := 430237738192465963717471

theorem tailTrace_7540965 : CollatzResearch.WordTrace tailWord_7540965 prefixEnd_7540965 430237738192465963717471 := by
  unfold tailWord_7540965
  simp only [CollatzResearch.WordTrace]
  refine ⟨275041589125379174132608349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183361059416919449421738899 275041589125379174132608349)
  ·
    refine ⟨103140595922017190299728131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275041589125379174132608349 103140595922017190299728131)
    ·
      refine ⟨154710893883025785449592197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103140595922017190299728131 154710893883025785449592197)
      ·
        refine ⟨29008292603067334771798537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154710893883025785449592197 29008292603067334771798537)
        ·
          refine ⟨21756219452300501078848903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29008292603067334771798537 21756219452300501078848903)
          ·
            refine ⟨32634329178450751618273355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21756219452300501078848903 32634329178450751618273355)
            ·
              refine ⟨48951493767676127427410033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32634329178450751618273355 48951493767676127427410033)
              ·
                refine ⟨36713620325757095570557525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48951493767676127427410033 36713620325757095570557525)
                ·
                  refine ⟨430237738192465963717471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36713620325757095570557525 430237738192465963717471)
                  ·
                    rfl

theorem cell23_7540965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_7540965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540965 prefixEnd_7540965 := by exact prefixLift 7540965
  have htrace : WordTrace (prefixWord ++ tailWord_7540965) baseStart_7540965 baseEnd_7540965 := by
    simpa [prefixWord, tailWord_7540965, baseEnd_7540965] using wordTrace_append hprefix tailTrace_7540965
  have hstable : (prefixWord ++ tailWord_7540965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540965).length < 2 ^ (prefixWord ++ tailWord_7540965).sum := by decide
  have hdescent : baseEnd_7540965 < baseStart_7540965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540986 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_7540986 : Nat := 118140960795 + 7540986 * 2 ^ 59
def prefixEnd_7540986 : Nat := 4983230072969 + 3 ^ 40 * 7540986 * 2
def baseEnd_7540986 : Nat := 1290716808941979363764881

theorem tailTrace_7540986 : CollatzResearch.WordTrace tailWord_7540986 prefixEnd_7540986 1290716808941979363764881 := by
  unfold tailWord_7540986
  simp only [CollatzResearch.WordTrace]
  refine ⟨68760588764575773679780703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183361570038868729812748541 68760588764575773679780703)
  ·
    refine ⟨103140883146863660519671055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68760588764575773679780703 103140883146863660519671055)
    ·
      refine ⟨154711324720295490779506583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103140883146863660519671055 154711324720295490779506583)
      ·
        refine ⟨232066987080443236169259875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154711324720295490779506583 232066987080443236169259875)
        ·
          refine ⟨348100480620664854253889813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232066987080443236169259875 348100480620664854253889813)
          ·
            refine ⟨16317210029093665043151085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 348100480620664854253889813 16317210029093665043151085)
            ·
              refine ⟨6118953760910124391181657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16317210029093665043151085 6118953760910124391181657)
              ·
                refine ⟨4589215320682593293386243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118953760910124391181657 4589215320682593293386243)
                ·
                  refine ⟨6883822981023889940079365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589215320682593293386243 6883822981023889940079365)
                  ·
                    refine ⟨1290716808941979363764881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883822981023889940079365 1290716808941979363764881)
                    ·
                      rfl

theorem cell23_7540986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_7540986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540986 prefixEnd_7540986 := by exact prefixLift 7540986
  have htrace : WordTrace (prefixWord ++ tailWord_7540986) baseStart_7540986 baseEnd_7540986 := by
    simpa [prefixWord, tailWord_7540986, baseEnd_7540986] using wordTrace_append hprefix tailTrace_7540986
  have hstable : (prefixWord ++ tailWord_7540986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540986).length < 2 ^ (prefixWord ++ tailWord_7540986).sum := by decide
  have hdescent : baseEnd_7540986 < baseStart_7540986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540995 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 3, 5]
def baseStart_7540995 : Nat := 118140960795 + 7540995 * 2 ^ 59
def prefixEnd_7540995 : Nat := 4983230072969 + 3 ^ 40 * 7540995 * 2
def baseEnd_7540995 : Nat := 1290718349383942852027367

theorem tailTrace_7540995 : CollatzResearch.WordTrace tailWord_7540995 prefixEnd_7540995 1290718349383942852027367 := by
  unfold tailWord_7540995
  simp only [CollatzResearch.WordTrace]
  refine ⟨275042683315270489256200439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183361788876846992837466959 275042683315270489256200439)
  ·
    refine ⟨412564024972905733884300659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275042683315270489256200439 412564024972905733884300659)
    ·
      refine ⟨618846037459358600826450989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412564024972905733884300659 618846037459358600826450989)
      ·
        refine ⟨232067264047259475309919121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618846037459358600826450989 232067264047259475309919121)
        ·
          refine ⟨174050448035444606482439341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232067264047259475309919121 174050448035444606482439341)
          ·
            refine ⟨65268918013291727430914753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174050448035444606482439341 65268918013291727430914753)
            ·
              refine ⟨48951688509968795573186065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65268918013291727430914753 48951688509968795573186065)
              ·
                refine ⟨36713766382476596679889549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48951688509968795573186065 36713766382476596679889549)
                ·
                  refine ⟨13767662393428723754958581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36713766382476596679889549 13767662393428723754958581)
                  ·
                    refine ⟨1290718349383942852027367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13767662393428723754958581 1290718349383942852027367)
                    ·
                      rfl

theorem cell23_7540995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 5].length) (baseStart_7540995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540995 prefixEnd_7540995 := by exact prefixLift 7540995
  have htrace : WordTrace (prefixWord ++ tailWord_7540995) baseStart_7540995 baseEnd_7540995 := by
    simpa [prefixWord, tailWord_7540995, baseEnd_7540995] using wordTrace_append hprefix tailTrace_7540995
  have hstable : (prefixWord ++ tailWord_7540995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540995).length < 2 ^ (prefixWord ++ tailWord_7540995).sum := by decide
  have hdescent : baseEnd_7540995 < baseStart_7540995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7540999 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 6]
def baseStart_7540999 : Nat := 118140960795 + 7540999 * 2 ^ 59
def prefixEnd_7540999 : Nat := 4983230072969 + 3 ^ 40 * 7540999 * 2
def baseEnd_7540999 : Nat := 430239678008271837825787

theorem tailTrace_7540999 : CollatzResearch.WordTrace tailWord_7540999 prefixEnd_7540999 430239678008271837825787 := by
  unfold tailWord_7540999
  simp only [CollatzResearch.WordTrace]
  refine ⟨275042829207255997939346051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183361886138170665292897367 275042829207255997939346051)
  ·
    refine ⟨412564243810883996909019077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275042829207255997939346051 412564243810883996909019077)
    ·
      refine ⟨77355795714540749420441077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412564243810883996909019077 77355795714540749420441077)
      ·
        refine ⟨7252105848238195258166351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77355795714540749420441077 7252105848238195258166351)
        ·
          refine ⟨10878158772357292887249527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252105848238195258166351 10878158772357292887249527)
          ·
            refine ⟨16317238158535939330874291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10878158772357292887249527 16317238158535939330874291)
            ·
              refine ⟨24475857237803908996311437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16317238158535939330874291 24475857237803908996311437)
              ·
                refine ⟨9178446464176465873616789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24475857237803908996311437 9178446464176465873616789)
                ·
                  refine ⟨430239678008271837825787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9178446464176465873616789 430239678008271837825787)
                  ·
                    rfl

theorem cell23_7540999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 6].length) (baseStart_7540999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7540999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7540999 prefixEnd_7540999 := by exact prefixLift 7540999
  have htrace : WordTrace (prefixWord ++ tailWord_7540999) baseStart_7540999 baseEnd_7540999 := by
    simpa [prefixWord, tailWord_7540999, baseEnd_7540999] using wordTrace_append hprefix tailTrace_7540999
  have hstable : (prefixWord ++ tailWord_7540999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7540999).length < 2 ^ (prefixWord ++ tailWord_7540999).sum := by decide
  have hdescent : baseEnd_7540999 < baseStart_7540999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7540999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541002 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2]
def baseStart_7541002 : Nat := 118140960795 + 7541002 * 2 ^ 59
def prefixEnd_7541002 : Nat := 4983230072969 + 3 ^ 40 * 7541002 * 2
def baseEnd_7541002 : Nat := 3872158642516410028694569

theorem tailTrace_7541002 : CollatzResearch.WordTrace tailWord_7541002 prefixEnd_7541002 3872158642516410028694569 := by
  unfold tailWord_7541002
  simp only [CollatzResearch.WordTrace]
  refine ⟨68760734656561282362926315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183361959084163419634470173 68760734656561282362926315)
  ·
    refine ⟨103141101984841923544389473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68760734656561282362926315 103141101984841923544389473)
    ·
      refine ⟨77355826488631442658292105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103141101984841923544389473 77355826488631442658292105)
      ·
        refine ⟨58016869866473581993719079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77355826488631442658292105 58016869866473581993719079)
        ·
          refine ⟨87025304799710372990578619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58016869866473581993719079 87025304799710372990578619)
          ·
            refine ⟨130537957199565559485867929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87025304799710372990578619 130537957199565559485867929)
            ·
              refine ⟨97903467899674169614400947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130537957199565559485867929 97903467899674169614400947)
              ·
                refine ⟨146855201849511254421601421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97903467899674169614400947 146855201849511254421601421)
                ·
                  refine ⟨55070700693566720408100533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146855201849511254421601421 55070700693566720408100533)
                  ·
                    refine ⟨5162878190021880038259425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55070700693566720408100533 5162878190021880038259425)
                    ·
                      refine ⟨3872158642516410028694569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162878190021880038259425 3872158642516410028694569)
                      ·
                        rfl

theorem cell23_7541002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_7541002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541002 prefixEnd_7541002 := by exact prefixLift 7541002
  have htrace : WordTrace (prefixWord ++ tailWord_7541002) baseStart_7541002 baseEnd_7541002 := by
    simpa [prefixWord, tailWord_7541002, baseEnd_7541002] using wordTrace_append hprefix tailTrace_7541002
  have hstable : (prefixWord ++ tailWord_7541002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541002).length < 2 ^ (prefixWord ++ tailWord_7541002).sum := by decide
  have hdescent : baseEnd_7541002 < baseStart_7541002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541025 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_7541025 : Nat := 118140960795 + 7541025 * 2 ^ 59
def prefixEnd_7541025 : Nat := 4983230072969 + 3 ^ 40 * 7541025 * 2
def baseEnd_7541025 : Nat := 1290723484190487812902321

theorem tailTrace_7541025 : CollatzResearch.WordTrace tailWord_7541025 prefixEnd_7541025 1290723484190487812902321 := by
  unfold tailWord_7541025
  simp only [CollatzResearch.WordTrace]
  refine ⟨275043777505161804379792529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183362518336774536253195019 275043777505161804379792529)
  ·
    refine ⟨206282833128871353284844397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275043777505161804379792529 206282833128871353284844397)
    ·
      refine ⟨77356062423326757481816649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206282833128871353284844397 77356062423326757481816649)
      ·
        refine ⟨58017046817495068111362487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77356062423326757481816649 58017046817495068111362487)
        ·
          refine ⟨87025570226242602167043731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58017046817495068111362487 87025570226242602167043731)
          ·
            refine ⟨130538355339363903250565597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87025570226242602167043731 130538355339363903250565597)
            ·
              refine ⟨48951883252261463718962099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130538355339363903250565597 48951883252261463718962099)
              ·
                refine ⟨73427824878392195578443149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48951883252261463718962099 73427824878392195578443149)
                ·
                  refine ⟨27535434329397073341916181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73427824878392195578443149 27535434329397073341916181)
                  ·
                    refine ⟨1290723484190487812902321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27535434329397073341916181 1290723484190487812902321)
                    ·
                      rfl

theorem cell23_7541025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_7541025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541025 prefixEnd_7541025 := by exact prefixLift 7541025
  have htrace : WordTrace (prefixWord ++ tailWord_7541025) baseStart_7541025 baseEnd_7541025 := by
    simpa [prefixWord, tailWord_7541025, baseEnd_7541025] using wordTrace_append hprefix tailTrace_7541025
  have hstable : (prefixWord ++ tailWord_7541025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541025).length < 2 ^ (prefixWord ++ tailWord_7541025).sum := by decide
  have hdescent : baseEnd_7541025 < baseStart_7541025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541037 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7541037 : Nat := 118140960795 + 7541037 * 2 ^ 59
def prefixEnd_7541037 : Nat := 4983230072969 + 3 ^ 40 * 7541037 * 2
def baseEnd_7541037 : Nat := 1290725538113105797252303

theorem tailTrace_7541037 : CollatzResearch.WordTrace tailWord_7541037 prefixEnd_7541037 1290725538113105797252303 := by
  unfold tailWord_7541037
  simp only [CollatzResearch.WordTrace]
  refine ⟨275044215181118330429229365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183362810120745553619486243 275044215181118330429229365)
  ·
    refine ⟨25785395173229843477740253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275044215181118330429229365 25785395173229843477740253)
    ·
      refine ⟨9669523189961191304152595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25785395173229843477740253 9669523189961191304152595)
      ·
        refine ⟨14504284784941786956228893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9669523189961191304152595 14504284784941786956228893)
        ·
          refine ⟨5439106794353170108585835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14504284784941786956228893 5439106794353170108585835)
          ·
            refine ⟨8158660191529755162878753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439106794353170108585835 8158660191529755162878753)
            ·
              refine ⟨6118995143647316372159065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8158660191529755162878753 6118995143647316372159065)
              ·
                refine ⟨4589246357735487279119299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6118995143647316372159065 4589246357735487279119299)
                ·
                  refine ⟨6883869536603230918678949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589246357735487279119299 6883869536603230918678949)
                  ·
                    refine ⟨1290725538113105797252303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883869536603230918678949 1290725538113105797252303)
                    ·
                      rfl

theorem cell23_7541037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7541037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541037 prefixEnd_7541037 := by exact prefixLift 7541037
  have htrace : WordTrace (prefixWord ++ tailWord_7541037) baseStart_7541037 baseEnd_7541037 := by
    simpa [prefixWord, tailWord_7541037, baseEnd_7541037] using wordTrace_append hprefix tailTrace_7541037
  have hstable : (prefixWord ++ tailWord_7541037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541037).length < 2 ^ (prefixWord ++ tailWord_7541037).sum := by decide
  have hdescent : baseEnd_7541037 < baseStart_7541037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541052 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_7541052 : Nat := 118140960795 + 7541052 * 2 ^ 59
def prefixEnd_7541052 : Nat := 4983230072969 + 3 ^ 40 * 7541052 * 2
def baseEnd_7541052 : Nat := 3872184316549134833069339

theorem tailTrace_7541052 : CollatzResearch.WordTrace tailWord_7541052 prefixEnd_7541052 3872184316549134833069339 := by
  unfold tailWord_7541052
  simp only [CollatzResearch.WordTrace]
  refine ⟨137522381138031993995512705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183363174850709325327350273 137522381138031993995512705)
  ·
    refine ⟨103141785853523995496634529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137522381138031993995512705 103141785853523995496634529)
    ·
      refine ⟨77356339390142996622475897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103141785853523995496634529 77356339390142996622475897)
      ·
        refine ⟨58017254542607247466856923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77356339390142996622475897 58017254542607247466856923)
        ·
          refine ⟨87025881813910871200285385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58017254542607247466856923 87025881813910871200285385)
          ·
            refine ⟨65269411360433153400214039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87025881813910871200285385 65269411360433153400214039)
            ·
              refine ⟨97904117040649730100321059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65269411360433153400214039 97904117040649730100321059)
              ·
                refine ⟨146856175560974595150481589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97904117040649730100321059 146856175560974595150481589)
                ·
                  refine ⟨13767766458841368295357649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146856175560974595150481589 13767766458841368295357649)
                  ·
                    refine ⟨10325824844131026221518237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13767766458841368295357649 10325824844131026221518237)
                    ·
                      refine ⟨3872184316549134833069339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10325824844131026221518237 3872184316549134833069339)
                      ·
                        rfl

theorem cell23_7541052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_7541052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541052 prefixEnd_7541052 := by exact prefixLift 7541052
  have htrace : WordTrace (prefixWord ++ tailWord_7541052) baseStart_7541052 baseEnd_7541052 := by
    simpa [prefixWord, tailWord_7541052, baseEnd_7541052] using wordTrace_append hprefix tailTrace_7541052
  have hstable : (prefixWord ++ tailWord_7541052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541052).length < 2 ^ (prefixWord ++ tailWord_7541052).sum := by decide
  have hdescent : baseEnd_7541052 < baseStart_7541052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541072 : List Nat := [2, 1, 1, 1, 1, 7, 3, 7]
def baseStart_7541072 : Nat := 118140960795 + 7541072 * 2 ^ 59
def prefixEnd_7541072 : Nat := 4983230072969 + 3 ^ 40 * 7541072 * 2
def baseEnd_7541072 : Nat := 143414614302304620548861

theorem tailTrace_7541072 : CollatzResearch.WordTrace tailWord_7541072 prefixEnd_7541072 143414614302304620548861 := by
  unfold tailWord_7541072
  simp only [CollatzResearch.WordTrace]
  refine ⟨137522745867995765703376735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183363661157327687604502313 137522745867995765703376735)
  ·
    refine ⟨206284118801993648555065103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137522745867995765703376735 206284118801993648555065103)
    ·
      refine ⟨309426178202990472832597655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206284118801993648555065103 309426178202990472832597655)
      ·
        refine ⟨464139267304485709248896483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309426178202990472832597655 464139267304485709248896483)
        ·
          refine ⟨696208900956728563873344725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464139267304485709248896483 696208900956728563873344725)
          ·
            refine ⟨16317396116173325715781517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 696208900956728563873344725 16317396116173325715781517)
            ·
              refine ⟨6119023543564997143418069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16317396116173325715781517 6119023543564997143418069)
              ·
                refine ⟨143414614302304620548861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6119023543564997143418069 143414614302304620548861)
                ·
                  rfl

theorem cell23_7541072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 7].length) (baseStart_7541072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541072 prefixEnd_7541072 := by exact prefixLift 7541072
  have htrace : WordTrace (prefixWord ++ tailWord_7541072) baseStart_7541072 baseEnd_7541072 := by
    simpa [prefixWord, tailWord_7541072, baseEnd_7541072] using wordTrace_append hprefix tailTrace_7541072
  have hstable : (prefixWord ++ tailWord_7541072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541072).length < 2 ^ (prefixWord ++ tailWord_7541072).sum := by decide
  have hdescent : baseEnd_7541072 < baseStart_7541072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541110 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_7541110 : Nat := 118140960795 + 7541110 * 2 ^ 59
def prefixEnd_7541110 : Nat := 4983230072969 + 3 ^ 40 * 7541110 * 2
def baseEnd_7541110 : Nat := 1290738032809031868714691

theorem tailTrace_7541110 : CollatzResearch.WordTrace tailWord_7541110 prefixEnd_7541110 1290738032809031868714691 := by
  unfold tailWord_7541110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190429856865866493539799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183364585139902575931091189 17190429856865866493539799)
  ·
    refine ⟨25785644785298799740309699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17190429856865866493539799 25785644785298799740309699)
    ·
      refine ⟨38678467177948199610464549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25785644785298799740309699 38678467177948199610464549)
      ·
        refine ⟨7252212595865287426962103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38678467177948199610464549 7252212595865287426962103)
        ·
          refine ⟨10878318893797931140443155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252212595865287426962103 10878318893797931140443155)
          ·
            refine ⟨16317478340696896710664733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10878318893797931140443155 16317478340696896710664733)
            ·
              refine ⟨6119054377761336266499275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16317478340696896710664733 6119054377761336266499275)
              ·
                refine ⟨9178581566642004399748913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6119054377761336266499275 9178581566642004399748913)
                ·
                  refine ⟨6883936174981503299811685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9178581566642004399748913 6883936174981503299811685)
                  ·
                    refine ⟨1290738032809031868714691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6883936174981503299811685 1290738032809031868714691)
                    ·
                      rfl

theorem cell23_7541110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_7541110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541110 prefixEnd_7541110 := by exact prefixLift 7541110
  have htrace : WordTrace (prefixWord ++ tailWord_7541110) baseStart_7541110 baseEnd_7541110 := by
    simpa [prefixWord, tailWord_7541110, baseEnd_7541110] using wordTrace_append hprefix tailTrace_7541110
  have hstable : (prefixWord ++ tailWord_7541110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541110).length < 2 ^ (prefixWord ++ tailWord_7541110).sum := by decide
  have hdescent : baseEnd_7541110 < baseStart_7541110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541156 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_7541156 : Nat := 118140960795 + 7541156 * 2 ^ 59
def prefixEnd_7541156 : Nat := 4983230072969 + 3 ^ 40 * 7541156 * 2
def baseEnd_7541156 : Nat := 3872237718537202426168861

theorem tailTrace_7541156 : CollatzResearch.WordTrace tailWord_7541156 prefixEnd_7541156 3872237718537202426168861 := by
  unfold tailWord_7541156
  simp only [CollatzResearch.WordTrace]
  refine ⟨137524277733843606876405661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183365703645124809168540881 137524277733843606876405661)
  ·
    refine ⟨51571604150191352578652123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137524277733843606876405661 51571604150191352578652123)
    ·
      refine ⟨77357406225287028867978185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51571604150191352578652123 77357406225287028867978185)
      ·
        refine ⟨58018054668965271650983639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77357406225287028867978185 58018054668965271650983639)
        ·
          refine ⟨87027082003447907476475459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58018054668965271650983639 87027082003447907476475459)
          ·
            refine ⟨130540623005171861214713189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87027082003447907476475459 130540623005171861214713189)
            ·
              refine ⟨24476366813469723977758723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130540623005171861214713189 24476366813469723977758723)
              ·
                refine ⟨36714550220204585966638085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24476366813469723977758723 36714550220204585966638085)
                ·
                  refine ⟨6883978166288359868744641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36714550220204585966638085 6883978166288359868744641)
                  ·
                    refine ⟨5162983624716269901558481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6883978166288359868744641 5162983624716269901558481)
                    ·
                      refine ⟨3872237718537202426168861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5162983624716269901558481 3872237718537202426168861)
                      ·
                        rfl

theorem cell23_7541156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_7541156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541156 prefixEnd_7541156 := by exact prefixLift 7541156
  have htrace : WordTrace (prefixWord ++ tailWord_7541156) baseStart_7541156 baseEnd_7541156 := by
    simpa [prefixWord, tailWord_7541156, baseEnd_7541156] using wordTrace_append hprefix tailTrace_7541156
  have hstable : (prefixWord ++ tailWord_7541156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541156).length < 2 ^ (prefixWord ++ tailWord_7541156).sum := by decide
  have hdescent : baseEnd_7541156 < baseStart_7541156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541206 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_7541206 : Nat := 118140960795 + 7541206 * 2 ^ 59
def prefixEnd_7541206 : Nat := 4983230072969 + 3 ^ 40 * 7541206 * 2
def baseEnd_7541206 : Nat := 3872263392569927230543631

theorem tailTrace_7541206 : CollatzResearch.WordTrace tailWord_7541206 prefixEnd_7541206 3872263392569927230543631 := by
  unfold tailWord_7541206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190648694844129518258217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183366919411670714861420981 17190648694844129518258217)
  ·
    refine ⟨12892986521133097138693663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17190648694844129518258217 12892986521133097138693663)
    ·
      refine ⟨19339479781699645708040495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12892986521133097138693663 19339479781699645708040495)
      ·
        refine ⟨29009219672549468562060743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19339479781699645708040495 29009219672549468562060743)
        ·
          refine ⟨43513829508824202843091115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29009219672549468562060743 43513829508824202843091115)
          ·
            refine ⟨65270744263236304264636673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43513829508824202843091115 65270744263236304264636673)
            ·
              refine ⟨48953058197427228198477505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65270744263236304264636673 48953058197427228198477505)
              ·
                refine ⟨36714793648070421148858129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48953058197427228198477505 36714793648070421148858129)
                ·
                  refine ⟨27536095236052815861643597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36714793648070421148858129 27536095236052815861643597)
                  ·
                    refine ⟨10326035713519805948116349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27536095236052815861643597 10326035713519805948116349)
                    ·
                      refine ⟨3872263392569927230543631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10326035713519805948116349 3872263392569927230543631)
                      ·
                        rfl

theorem cell23_7541206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_7541206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541206 prefixEnd_7541206 := by exact prefixLift 7541206
  have htrace : WordTrace (prefixWord ++ tailWord_7541206) baseStart_7541206 baseEnd_7541206 := by
    simpa [prefixWord, tailWord_7541206, baseEnd_7541206] using wordTrace_append hprefix tailTrace_7541206
  have hstable : (prefixWord ++ tailWord_7541206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541206).length < 2 ^ (prefixWord ++ tailWord_7541206).sum := by decide
  have hdescent : baseEnd_7541206 < baseStart_7541206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541242 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_7541242 : Nat := 118140960795 + 7541242 * 2 ^ 59
def prefixEnd_7541242 : Nat := 4983230072969 + 3 ^ 40 * 7541242 * 2
def baseEnd_7541242 : Nat := 3872281877873489089693465

theorem tailTrace_7541242 : CollatzResearch.WordTrace tailWord_7541242 prefixEnd_7541242 3872281877873489089693465 := by
  unfold tailWord_7541242
  simp only [CollatzResearch.WordTrace]
  refine ⟨68762923036343912610110495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183367794763583766960294653 68762923036343912610110495)
  ·
    refine ⟨103144384554515868915165743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68762923036343912610110495 103144384554515868915165743)
    ·
      refine ⟨154716576831773803372748615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103144384554515868915165743 154716576831773803372748615)
      ·
        refine ⟨232074865247660705059122923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154716576831773803372748615 232074865247660705059122923)
        ·
          refine ⟨348112297871491057588684385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232074865247660705059122923 348112297871491057588684385)
          ·
            refine ⟨261084223403618293191513289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348112297871491057588684385 261084223403618293191513289)
            ·
              refine ⟨195813167552713719893634967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261084223403618293191513289 195813167552713719893634967)
              ·
                refine ⟨293719751329070579840452451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195813167552713719893634967 293719751329070579840452451)
                ·
                  refine ⟨440579626993605869760678677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293719751329070579840452451 440579626993605869760678677)
                  ·
                    refine ⟨20652170015325275145031813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 440579626993605869760678677 20652170015325275145031813)
                    ·
                      refine ⟨3872281877873489089693465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20652170015325275145031813 3872281877873489089693465)
                      ·
                        rfl

theorem cell23_7541242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_7541242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541242 prefixEnd_7541242 := by exact prefixLift 7541242
  have htrace : WordTrace (prefixWord ++ tailWord_7541242) baseStart_7541242 baseEnd_7541242 := by
    simpa [prefixWord, tailWord_7541242, baseEnd_7541242] using wordTrace_append hprefix tailTrace_7541242
  have hstable : (prefixWord ++ tailWord_7541242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541242).length < 2 ^ (prefixWord ++ tailWord_7541242).sum := by decide
  have hdescent : baseEnd_7541242 < baseStart_7541242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541292 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_7541292 : Nat := 118140960795 + 7541292 * 2 ^ 59
def prefixEnd_7541292 : Nat := 4983230072969 + 3 ^ 40 * 7541292 * 2
def baseEnd_7541292 : Nat := 3872307551906213894068235

theorem tailTrace_7541292 : CollatzResearch.WordTrace tailWord_7541292 prefixEnd_7541292 3872307551906213894068235 := by
  unfold tailWord_7541292
  simp only [CollatzResearch.WordTrace]
  refine ⟨137526757897597254489881065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183369010530129672653174753 137526757897597254489881065)
  ·
    refine ⟨103145068423197940867410799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137526757897597254489881065 103145068423197940867410799)
    ·
      refine ⟨154717602634796911301116199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103145068423197940867410799 154717602634796911301116199)
      ·
        refine ⟨232076403952195366951674299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154717602634796911301116199 232076403952195366951674299)
        ·
          refine ⟨348114605928293050427511449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232076403952195366951674299 348114605928293050427511449)
          ·
            refine ⟨261085954446219787820633587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348114605928293050427511449 261085954446219787820633587)
            ·
              refine ⟨391628931669329681730950381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261085954446219787820633587 391628931669329681730950381)
              ·
                refine ⟨146860849375998630649106393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391628931669329681730950381 146860849375998630649106393)
                ·
                  refine ⟨110145637031998972986829795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146860849375998630649106393 110145637031998972986829795)
                  ·
                    refine ⟨165218455547998459480244693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110145637031998972986829795 165218455547998459480244693)
                    ·
                      refine ⟨3872307551906213894068235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165218455547998459480244693 3872307551906213894068235)
                      ·
                        rfl

theorem cell23_7541292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_7541292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541292 prefixEnd_7541292 := by exact prefixLift 7541292
  have htrace : WordTrace (prefixWord ++ tailWord_7541292) baseStart_7541292 baseEnd_7541292 := by
    simpa [prefixWord, tailWord_7541292, baseEnd_7541292] using wordTrace_append hprefix tailTrace_7541292
  have hstable : (prefixWord ++ tailWord_7541292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541292).length < 2 ^ (prefixWord ++ tailWord_7541292).sum := by decide
  have hdescent : baseEnd_7541292 < baseStart_7541292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541296 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3]
def baseStart_7541296 : Nat := 118140960795 + 7541296 * 2 ^ 59
def prefixEnd_7541296 : Nat := 4983230072969 + 3 ^ 40 * 7541296 * 2
def baseEnd_7541296 : Nat := 3872309605828831878418217

theorem tailTrace_7541296 : CollatzResearch.WordTrace tailWord_7541296 prefixEnd_7541296 3872309605828831878418217 := by
  unfold tailWord_7541296
  simp only [CollatzResearch.WordTrace]
  refine ⟨137526830843590008831453871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183369107791453345108605161 137526830843590008831453871)
  ·
    refine ⟨206290246265385013247180807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137526830843590008831453871 206290246265385013247180807)
    ·
      refine ⟨309435369398077519870771211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206290246265385013247180807 309435369398077519870771211)
      ·
        refine ⟨464153054097116279806156817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309435369398077519870771211 464153054097116279806156817)
        ·
          refine ⟨348114790572837209854617613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464153054097116279806156817 348114790572837209854617613)
          ·
            refine ⟨130543046464813953695481605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348114790572837209854617613 130543046464813953695481605)
            ·
              refine ⟨24476821212152616317902801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130543046464813953695481605 24476821212152616317902801)
              ·
                refine ⟨18357615909114462238427101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24476821212152616317902801 18357615909114462238427101)
                ·
                  refine ⟨6884105965917923339410163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18357615909114462238427101 6884105965917923339410163)
                  ·
                    refine ⟨10326158948876885009115245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6884105965917923339410163 10326158948876885009115245)
                    ·
                      refine ⟨3872309605828831878418217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10326158948876885009115245 3872309605828831878418217)
                      ·
                        rfl

theorem cell23_7541296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_7541296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541296 prefixEnd_7541296 := by exact prefixLift 7541296
  have htrace : WordTrace (prefixWord ++ tailWord_7541296) baseStart_7541296 baseEnd_7541296 := by
    simpa [prefixWord, tailWord_7541296, baseEnd_7541296] using wordTrace_append hprefix tailTrace_7541296
  have hstable : (prefixWord ++ tailWord_7541296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541296).length < 2 ^ (prefixWord ++ tailWord_7541296).sum := by decide
  have hdescent : baseEnd_7541296 < baseStart_7541296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541306 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2]
def baseStart_7541306 : Nat := 118140960795 + 7541306 * 2 ^ 59
def prefixEnd_7541306 : Nat := 4983230072969 + 3 ^ 40 * 7541306 * 2
def baseEnd_7541306 : Nat := 3872314740635376839293171

theorem tailTrace_7541306 : CollatzResearch.WordTrace tailWord_7541306 prefixEnd_7541306 3872314740635376839293171 := by
  unfold tailWord_7541306
  simp only [CollatzResearch.WordTrace]
  refine ⟨68763506604285947342692943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183369350944762526247181181 68763506604285947342692943)
  ·
    refine ⟨103145259906428921014039415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68763506604285947342692943 103145259906428921014039415)
    ·
      refine ⟨154717889859643381521059123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103145259906428921014039415 154717889859643381521059123)
      ·
        refine ⟨232076834789465072281588685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154717889859643381521059123 232076834789465072281588685)
        ·
          refine ⟨87028813046049402105595757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232076834789465072281588685 87028813046049402105595757)
          ·
            refine ⟨32635804892268525789598409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87028813046049402105595757 32635804892268525789598409)
            ·
              refine ⟨24476853669201394342198807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32635804892268525789598409 24476853669201394342198807)
              ·
                refine ⟨36715280503802091513298211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24476853669201394342198807 36715280503802091513298211)
                ·
                  refine ⟨55072920755703137269947317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36715280503802091513298211 55072920755703137269947317)
                  ·
                    refine ⟨5163086320847169119057561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55072920755703137269947317 5163086320847169119057561)
                    ·
                      refine ⟨3872314740635376839293171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163086320847169119057561 3872314740635376839293171)
                      ·
                        rfl

theorem cell23_7541306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_7541306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541306 prefixEnd_7541306 := by exact prefixLift 7541306
  have htrace : WordTrace (prefixWord ++ tailWord_7541306) baseStart_7541306 baseEnd_7541306 := by
    simpa [prefixWord, tailWord_7541306, baseEnd_7541306] using wordTrace_append hprefix tailTrace_7541306
  have hstable : (prefixWord ++ tailWord_7541306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541306).length < 2 ^ (prefixWord ++ tailWord_7541306).sum := by decide
  have hdescent : baseEnd_7541306 < baseStart_7541306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541373 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_7541373 : Nat := 118140960795 + 7541373 * 2 ^ 59
def prefixEnd_7541373 : Nat := 4983230072969 + 3 ^ 40 * 7541373 * 2
def baseEnd_7541373 : Nat := 3872349143839228077155363

theorem tailTrace_7541373 : CollatzResearch.WordTrace tailWord_7541373 prefixEnd_7541373 3872349143839228077155363 := by
  unfold tailWord_7541373
  simp only [CollatzResearch.WordTrace]
  refine ⟨275056470107901059813460773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183370980071934039875640515 275056470107901059813460773)
  ·
    refine ⟨51573088145231448715023895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275056470107901059813460773 51573088145231448715023895)
    ·
      refine ⟨77359632217847173072535843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51573088145231448715023895 77359632217847173072535843)
      ·
        refine ⟨116039448326770759608803765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77359632217847173072535843 116039448326770759608803765)
        ·
          refine ⟨10878698280634758713325353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116039448326770759608803765 10878698280634758713325353)
          ·
            refine ⟨8159023710476069034994015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878698280634758713325353 8159023710476069034994015)
            ·
              refine ⟨12238535565714103552491023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159023710476069034994015 12238535565714103552491023)
              ·
                refine ⟨18357803348571155328736535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12238535565714103552491023 18357803348571155328736535)
                ·
                  refine ⟨27536705022856732993104803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18357803348571155328736535 27536705022856732993104803)
                  ·
                    refine ⟨41305057534285099489657205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27536705022856732993104803 41305057534285099489657205)
                    ·
                      refine ⟨3872349143839228077155363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41305057534285099489657205 3872349143839228077155363)
                      ·
                        rfl

theorem cell23_7541373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_7541373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541373 prefixEnd_7541373 := by exact prefixLift 7541373
  have htrace : WordTrace (prefixWord ++ tailWord_7541373) baseStart_7541373 baseEnd_7541373 := by
    simpa [prefixWord, tailWord_7541373, baseEnd_7541373] using wordTrace_append hprefix tailTrace_7541373
  have hstable : (prefixWord ++ tailWord_7541373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541373).length < 2 ^ (prefixWord ++ tailWord_7541373).sum := by decide
  have hdescent : baseEnd_7541373 < baseStart_7541373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541406 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_7541406 : Nat := 118140960795 + 7541406 * 2 ^ 59
def prefixEnd_7541406 : Nat := 4983230072969 + 3 ^ 40 * 7541406 * 2
def baseEnd_7541406 : Nat := 1290788696233608816014237

theorem tailTrace_7541406 : CollatzResearch.WordTrace tailWord_7541406 prefixEnd_7541406 1290788696233608816014237 := by
  unfold tailWord_7541406
  simp only [CollatzResearch.WordTrace]
  refine ⟨34382209214597688306176509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183371782477854337632941381 34382209214597688306176509)
  ·
    refine ⟨12893328455474133114816191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34382209214597688306176509 12893328455474133114816191)
    ·
      refine ⟨19339992683211199672224287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12893328455474133114816191 19339992683211199672224287)
      ·
        refine ⟨29009989024816799508336431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19339992683211199672224287 29009989024816799508336431)
        ·
          refine ⟨43514983537225199262504647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29009989024816799508336431 43514983537225199262504647)
          ·
            refine ⟨65272475305837798893756971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43514983537225199262504647 65272475305837798893756971)
            ·
              refine ⟨97908712958756698340635457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65272475305837798893756971 97908712958756698340635457)
              ·
                refine ⟨73431534719067523755476593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97908712958756698340635457 73431534719067523755476593)
                ·
                  refine ⟨55073651039300642816607445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73431534719067523755476593 55073651039300642816607445)
                  ·
                    refine ⟨1290788696233608816014237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55073651039300642816607445 1290788696233608816014237)
                    ·
                      rfl

theorem cell23_7541406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_7541406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541406 prefixEnd_7541406 := by exact prefixLift 7541406
  have htrace : WordTrace (prefixWord ++ tailWord_7541406) baseStart_7541406 baseEnd_7541406 := by
    simpa [prefixWord, tailWord_7541406, baseEnd_7541406] using wordTrace_append hprefix tailTrace_7541406
  have hstable : (prefixWord ++ tailWord_7541406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541406).length < 2 ^ (prefixWord ++ tailWord_7541406).sum := by decide
  have hdescent : baseEnd_7541406 < baseStart_7541406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541413 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_7541413 : Nat := 118140960795 + 7541413 * 2 ^ 59
def prefixEnd_7541413 : Nat := 4983230072969 + 3 ^ 40 * 7541413 * 2
def baseEnd_7541413 : Nat := 3872369683065407920655179

theorem tailTrace_7541413 : CollatzResearch.WordTrace tailWord_7541413 prefixEnd_7541413 3872369683065407920655179 := by
  unfold tailWord_7541413
  simp only [CollatzResearch.WordTrace]
  refine ⟨275057929027756146644916893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183371952685170764429944595 275057929027756146644916893)
  ·
    refine ⟨103146723385408554991843835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275057929027756146644916893 103146723385408554991843835)
    ·
      refine ⟨154720085078112832487765753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103146723385408554991843835 154720085078112832487765753)
      ·
        refine ⟨116040063808584624365824315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154720085078112832487765753 116040063808584624365824315)
        ·
          refine ⟨174060095712876936548736473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116040063808584624365824315 174060095712876936548736473)
          ·
            refine ⟨130545071784657702411552355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174060095712876936548736473 130545071784657702411552355)
            ·
              refine ⟨195817607676986553617328533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130545071784657702411552355 195817607676986553617328533)
              ·
                refine ⟨9178950359858744700812275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195817607676986553617328533 9178950359858744700812275)
                ·
                  refine ⟨13768425539788117051218413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9178950359858744700812275 13768425539788117051218413)
                  ·
                    refine ⟨5163159577420543894206905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13768425539788117051218413 5163159577420543894206905)
                    ·
                      refine ⟨3872369683065407920655179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163159577420543894206905 3872369683065407920655179)
                      ·
                        rfl

theorem cell23_7541413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_7541413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541413 prefixEnd_7541413 := by exact prefixLift 7541413
  have htrace : WordTrace (prefixWord ++ tailWord_7541413) baseStart_7541413 baseEnd_7541413 := by
    simpa [prefixWord, tailWord_7541413, baseEnd_7541413] using wordTrace_append hprefix tailTrace_7541413
  have hstable : (prefixWord ++ tailWord_7541413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541413).length < 2 ^ (prefixWord ++ tailWord_7541413).sum := by decide
  have hdescent : baseEnd_7541413 < baseStart_7541413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541496 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_7541496 : Nat := 118140960795 + 7541496 * 2 ^ 59
def prefixEnd_7541496 : Nat := 4983230072969 + 3 ^ 40 * 7541496 * 2
def baseEnd_7541496 : Nat := 1290804100653243698639099

theorem tailTrace_7541496 : CollatzResearch.WordTrace tailWord_7541496 prefixEnd_7541496 1290804100653243698639099 := by
  unfold tailWord_7541496
  simp only [CollatzResearch.WordTrace]
  refine ⟨137530478143227725910094171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183373970857636967880125561 137530478143227725910094171)
  ·
    refine ⟨206295717214841588865141257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137530478143227725910094171 206295717214841588865141257)
    ·
      refine ⟨154721787911131191648855943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206295717214841588865141257 154721787911131191648855943)
      ·
        refine ⟨232082681866696787473283915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154721787911131191648855943 232082681866696787473283915)
        ·
          refine ⟨348124022800045181209925873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232082681866696787473283915 348124022800045181209925873)
          ·
            refine ⟨261093017100033885907444405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348124022800045181209925873 261093017100033885907444405)
            ·
              refine ⟨24477470353128176803822913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261093017100033885907444405 24477470353128176803822913)
              ·
                refine ⟨18358102764846132602867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24477470353128176803822913 18358102764846132602867185)
                ·
                  refine ⟨13768577073634599452150389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18358102764846132602867185 13768577073634599452150389)
                  ·
                    refine ⟨1290804100653243698639099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13768577073634599452150389 1290804100653243698639099)
                    ·
                      rfl

theorem cell23_7541496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_7541496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541496 prefixEnd_7541496 := by exact prefixLift 7541496
  have htrace : WordTrace (prefixWord ++ tailWord_7541496) baseStart_7541496 baseEnd_7541496 := by
    simpa [prefixWord, tailWord_7541496, baseEnd_7541496] using wordTrace_append hprefix tailTrace_7541496
  have hstable : (prefixWord ++ tailWord_7541496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541496).length < 2 ^ (prefixWord ++ tailWord_7541496).sum := by decide
  have hdescent : baseEnd_7541496 < baseStart_7541496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541500 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 5]
def baseStart_7541500 : Nat := 118140960795 + 7541500 * 2 ^ 59
def prefixEnd_7541500 : Nat := 4983230072969 + 3 ^ 40 * 7541500 * 2
def baseEnd_7541500 : Nat := 430268261764705453363031

theorem tailTrace_7541500 : CollatzResearch.WordTrace tailWord_7541500 prefixEnd_7541500 430268261764705453363031 := by
  unfold tailWord_7541500
  simp only [CollatzResearch.WordTrace]
  refine ⟨137530551089220480251666977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183374068118960640335555969 137530551089220480251666977)
  ·
    refine ⟨103147913316915360188750233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137530551089220480251666977 103147913316915360188750233)
    ·
      refine ⟨77360934987686520141562675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103147913316915360188750233 77360934987686520141562675)
      ·
        refine ⟨116041402481529780212344013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77360934987686520141562675 116041402481529780212344013)
        ·
          refine ⟨43515525930573667579629005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116041402481529780212344013 43515525930573667579629005)
          ·
            refine ⟨16318322223965125342360877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43515525930573667579629005 16318322223965125342360877)
            ·
              refine ⟨6119370833986922003385329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16318322223965125342360877 6119370833986922003385329)
              ·
                refine ⟨4589528125490191502538997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6119370833986922003385329 4589528125490191502538997)
                ·
                  refine ⟨430268261764705453363031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4589528125490191502538997 430268261764705453363031)
                  ·
                    rfl

theorem cell23_7541500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_7541500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541500 prefixEnd_7541500 := by exact prefixLift 7541500
  have htrace : WordTrace (prefixWord ++ tailWord_7541500) baseStart_7541500 baseEnd_7541500 := by
    simpa [prefixWord, tailWord_7541500, baseEnd_7541500] using wordTrace_append hprefix tailTrace_7541500
  have hstable : (prefixWord ++ tailWord_7541500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541500).length < 2 ^ (prefixWord ++ tailWord_7541500).sum := by decide
  have hdescent : baseEnd_7541500 < baseStart_7541500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541516 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7541516 : Nat := 118140960795 + 7541516 * 2 ^ 59
def prefixEnd_7541516 : Nat := 4983230072969 + 3 ^ 40 * 7541516 * 2
def baseEnd_7541516 : Nat := 3872422571572821017667205

theorem tailTrace_7541516 : CollatzResearch.WordTrace tailWord_7541516 prefixEnd_7541516 3872422571572821017667205 := by
  unfold tailWord_7541516
  simp only [CollatzResearch.WordTrace]
  refine ⟨137530842873191497617958201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183374457164255330157277601 137530842873191497617958201)
  ·
    refine ⟨103148132154893623213468651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137530842873191497617958201 103148132154893623213468651)
    ·
      refine ⟨154722198232340434820202977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103148132154893623213468651 154722198232340434820202977)
      ·
        refine ⟨116041648674255326115152233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154722198232340434820202977 116041648674255326115152233)
        ·
          refine ⟨87031236505691494586364175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116041648674255326115152233 87031236505691494586364175)
          ·
            refine ⟨130546854758537241879546263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87031236505691494586364175 130546854758537241879546263)
            ·
              refine ⟨195820282137805862819319395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130546854758537241879546263 195820282137805862819319395)
              ·
                refine ⟨293730423206708794228979093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195820282137805862819319395 293730423206708794228979093)
                ·
                  refine ⟨13768613587814474729483395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293730423206708794228979093 13768613587814474729483395)
                  ·
                    refine ⟨20652920381721712094225093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13768613587814474729483395 20652920381721712094225093)
                    ·
                      refine ⟨3872422571572821017667205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20652920381721712094225093 3872422571572821017667205)
                      ·
                        rfl

theorem cell23_7541516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7541516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541516 prefixEnd_7541516 := by exact prefixLift 7541516
  have htrace : WordTrace (prefixWord ++ tailWord_7541516) baseStart_7541516 baseEnd_7541516 := by
    simpa [prefixWord, tailWord_7541516, baseEnd_7541516] using wordTrace_append hprefix tailTrace_7541516
  have hstable : (prefixWord ++ tailWord_7541516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541516).length < 2 ^ (prefixWord ++ tailWord_7541516).sum := by decide
  have hdescent : baseEnd_7541516 < baseStart_7541516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541550 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7541550 : Nat := 118140960795 + 7541550 * 2 ^ 59
def prefixEnd_7541550 : Nat := 4983230072969 + 3 ^ 40 * 7541550 * 2
def baseEnd_7541550 : Nat := 3872440029915073884642049

theorem tailTrace_7541550 : CollatzResearch.WordTrace tailWord_7541550 prefixEnd_7541550 3872440029915073884642049 := by
  unfold tailWord_7541550
  simp only [CollatzResearch.WordTrace]
  refine ⟨34382865728532477380331763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183375283885506546028436069 34382865728532477380331763)
  ·
    refine ⟨51574298592798716070497645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34382865728532477380331763 51574298592798716070497645)
    ·
      refine ⟨19340361972299518526436617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51574298592798716070497645 19340361972299518526436617)
      ·
        refine ⟨14505271479224638894827463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19340361972299518526436617 14505271479224638894827463)
        ·
          refine ⟨21757907218836958342241195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14505271479224638894827463 21757907218836958342241195)
          ·
            refine ⟨32636860828255437513361793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21757907218836958342241195 32636860828255437513361793)
            ·
              refine ⟨24477645621191578135021345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32636860828255437513361793 24477645621191578135021345)
              ·
                refine ⟨18358234215893683601266009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24477645621191578135021345 18358234215893683601266009)
                ·
                  refine ⟨13768675661920262700949507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18358234215893683601266009 13768675661920262700949507)
                  ·
                    refine ⟨20653013492880394051424261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13768675661920262700949507 20653013492880394051424261)
                    ·
                      refine ⟨3872440029915073884642049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20653013492880394051424261 3872440029915073884642049)
                      ·
                        rfl

theorem cell23_7541550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7541550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541550 prefixEnd_7541550 := by exact prefixLift 7541550
  have htrace : WordTrace (prefixWord ++ tailWord_7541550) baseStart_7541550 baseEnd_7541550 := by
    simpa [prefixWord, tailWord_7541550, baseEnd_7541550] using wordTrace_append hprefix tailTrace_7541550
  have hstable : (prefixWord ++ tailWord_7541550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541550).length < 2 ^ (prefixWord ++ tailWord_7541550).sum := by decide
  have hdescent : baseEnd_7541550 < baseStart_7541550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541553 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_7541553 : Nat := 118140960795 + 7541553 * 2 ^ 59
def prefixEnd_7541553 : Nat := 4983230072969 + 3 ^ 40 * 7541553 * 2
def baseEnd_7541553 : Nat := 3872441570357037372904535

theorem tailTrace_7541553 : CollatzResearch.WordTrace tailWord_7541553 prefixEnd_7541553 3872441570357037372904535 := by
  unfold tailWord_7541553
  simp only [CollatzResearch.WordTrace]
  refine ⟨275063035247248950555013313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183375356831499300370008875 275063035247248950555013313)
  ·
    refine ⟨206297276435436712916259985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275063035247248950555013313 206297276435436712916259985)
    ·
      refine ⟨154722957326577534687194989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206297276435436712916259985 154722957326577534687194989)
      ·
        refine ⟨58021108997466575507698121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154722957326577534687194989 58021108997466575507698121)
        ·
          refine ⟨43515831748099931630773591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58021108997466575507698121 43515831748099931630773591)
          ·
            refine ⟨65273747622149897446160387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43515831748099931630773591 65273747622149897446160387)
            ·
              refine ⟨97910621433224846169240581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65273747622149897446160387 97910621433224846169240581)
              ·
                refine ⟨18358241518729658656732609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97910621433224846169240581 18358241518729658656732609)
                ·
                  refine ⟨13768681139047243992549457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18358241518729658656732609 13768681139047243992549457)
                  ·
                    refine ⟨10326510854285432994412093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13768681139047243992549457 10326510854285432994412093)
                    ·
                      refine ⟨3872441570357037372904535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10326510854285432994412093 3872441570357037372904535)
                      ·
                        rfl

theorem cell23_7541553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_7541553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541553 prefixEnd_7541553 := by exact prefixLift 7541553
  have htrace : WordTrace (prefixWord ++ tailWord_7541553) baseStart_7541553 baseEnd_7541553 := by
    simpa [prefixWord, tailWord_7541553, baseEnd_7541553] using wordTrace_append hprefix tailTrace_7541553
  have hstable : (prefixWord ++ tailWord_7541553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541553).length < 2 ^ (prefixWord ++ tailWord_7541553).sum := by decide
  have hdescent : baseEnd_7541553 < baseStart_7541553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541560 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 1, 4]
def baseStart_7541560 : Nat := 118140960795 + 7541560 * 2 ^ 59
def prefixEnd_7541560 : Nat := 4983230072969 + 3 ^ 40 * 7541560 * 2
def baseEnd_7541560 : Nat := 1290815054907206281839001

theorem tailTrace_7541560 : CollatzResearch.WordTrace tailWord_7541560 prefixEnd_7541560 1290815054907206281839001 := by
  unfold tailWord_7541560
  simp only [CollatzResearch.WordTrace]
  refine ⟨137531645279111795375259067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183375527038815727167012089 137531645279111795375259067)
  ·
    refine ⟨206297467918667693062888601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137531645279111795375259067 206297467918667693062888601)
    ·
      refine ⟨154723100939000769797166451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206297467918667693062888601 154723100939000769797166451)
      ·
        refine ⟨232084651408501154695749677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154723100939000769797166451 232084651408501154695749677)
        ·
          refine ⟨87031744278187933010906129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232084651408501154695749677 87031744278187933010906129)
          ·
            refine ⟨65273808208640949758179597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87031744278187933010906129 65273808208640949758179597)
            ·
              refine ⟨24477678078240356159317349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65273808208640949758179597 24477678078240356159317349)
              ·
                refine ⟨4589564639670066779872003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24477678078240356159317349 4589564639670066779872003)
                ·
                  refine ⟨6884346959505100169808005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589564639670066779872003 6884346959505100169808005)
                  ·
                    refine ⟨1290815054907206281839001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884346959505100169808005 1290815054907206281839001)
                    ·
                      rfl

theorem cell23_7541560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_7541560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541560 prefixEnd_7541560 := by exact prefixLift 7541560
  have htrace : WordTrace (prefixWord ++ tailWord_7541560) baseStart_7541560 baseEnd_7541560 := by
    simpa [prefixWord, tailWord_7541560, baseEnd_7541560] using wordTrace_append hprefix tailTrace_7541560
  have hstable : (prefixWord ++ tailWord_7541560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541560).length < 2 ^ (prefixWord ++ tailWord_7541560).sum := by decide
  have hdescent : baseEnd_7541560 < baseStart_7541560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541616 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_7541616 : Nat := 118140960795 + 7541616 * 2 ^ 59
def prefixEnd_7541616 : Nat := 4983230072969 + 3 ^ 40 * 7541616 * 2
def baseEnd_7541616 : Nat := 1290824639879423542138915

theorem tailTrace_7541616 : CollatzResearch.WordTrace tailWord_7541616 prefixEnd_7541616 1290824639879423542138915 := by
  unfold tailWord_7541616
  simp only [CollatzResearch.WordTrace]
  refine ⟨137532666523010356157278351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183376888697347141543037801 137532666523010356157278351)
  ·
    refine ⟨206298999784515534235917527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137532666523010356157278351 206298999784515534235917527)
    ·
      refine ⟨309448499676773301353876291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206298999784515534235917527 309448499676773301353876291)
      ·
        refine ⟨464172749515159952030814437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309448499676773301353876291 464172749515159952030814437)
        ·
          refine ⟨87032390534092491005777707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464172749515159952030814437 87032390534092491005777707)
          ·
            refine ⟨130548585801138736508666561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87032390534092491005777707 130548585801138736508666561)
            ·
              refine ⟨97911439350854052381499921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130548585801138736508666561 97911439350854052381499921)
              ·
                refine ⟨73433579513140539286124941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97911439350854052381499921 73433579513140539286124941)
                ·
                  refine ⟨27537592317427702232296853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73433579513140539286124941 27537592317427702232296853)
                  ·
                    refine ⟨1290824639879423542138915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27537592317427702232296853 1290824639879423542138915)
                    ·
                      rfl

theorem cell23_7541616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_7541616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541616 prefixEnd_7541616 := by exact prefixLift 7541616
  have htrace : WordTrace (prefixWord ++ tailWord_7541616) baseStart_7541616 baseEnd_7541616 := by
    simpa [prefixWord, tailWord_7541616, baseEnd_7541616] using wordTrace_append hprefix tailTrace_7541616
  have hstable : (prefixWord ++ tailWord_7541616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541616).length < 2 ^ (prefixWord ++ tailWord_7541616).sum := by decide
  have hdescent : baseEnd_7541616 < baseStart_7541616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541617 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 1, 1, 3]
def baseStart_7541617 : Nat := 118140960795 + 7541617 * 2 ^ 59
def prefixEnd_7541617 : Nat := 4983230072969 + 3 ^ 40 * 7541617 * 2
def baseEnd_7541617 : Nat := 3872474433118925122504241

theorem tailTrace_7541617 : CollatzResearch.WordTrace tailWord_7541617 prefixEnd_7541617 3872474433118925122504241 := by
  unfold tailWord_7541617
  simp only [CollatzResearch.WordTrace]
  refine ⟨275065369519017089485343105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183376913012678059656895403 275065369519017089485343105)
  ·
    refine ⟨206299027139262817114007329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275065369519017089485343105 206299027139262817114007329)
    ·
      refine ⟨154724270354447112835505497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206299027139262817114007329 154724270354447112835505497)
      ·
        refine ⟨116043202765835334626629123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154724270354447112835505497 116043202765835334626629123)
        ·
          refine ⟨174064804148753001939943685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116043202765835334626629123 174064804148753001939943685)
          ·
            refine ⟨32637150777891187863739441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174064804148753001939943685 32637150777891187863739441)
            ·
              refine ⟨24477863083418390897804581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32637150777891187863739441 24477863083418390897804581)
              ·
                refine ⟨4589599328140948293338359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24477863083418390897804581 4589599328140948293338359)
                ·
                  refine ⟨6884398992211422440007539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4589599328140948293338359 6884398992211422440007539)
                  ·
                    refine ⟨10326598488317133660011309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6884398992211422440007539 10326598488317133660011309)
                    ·
                      refine ⟨3872474433118925122504241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10326598488317133660011309 3872474433118925122504241)
                      ·
                        rfl

theorem cell23_7541617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_7541617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541617 prefixEnd_7541617 := by exact prefixLift 7541617
  have htrace : WordTrace (prefixWord ++ tailWord_7541617) baseStart_7541617 baseEnd_7541617 := by
    simpa [prefixWord, tailWord_7541617, baseEnd_7541617] using wordTrace_append hprefix tailTrace_7541617
  have hstable : (prefixWord ++ tailWord_7541617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541617).length < 2 ^ (prefixWord ++ tailWord_7541617).sum := by decide
  have hdescent : baseEnd_7541617 < baseStart_7541617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541640 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7541640 : Nat := 118140960795 + 7541640 * 2 ^ 59
def prefixEnd_7541640 : Nat := 4983230072969 + 3 ^ 40 * 7541640 * 2
def baseEnd_7541640 : Nat := 3872486243173978532516635

theorem tailTrace_7541640 : CollatzResearch.WordTrace tailWord_7541640 prefixEnd_7541640 3872486243173978532516635 := by
  unfold tailWord_7541640
  simp only [CollatzResearch.WordTrace]
  refine ⟨137533104198966882206715187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183377472265289176275620249 137533104198966882206715187)
  ·
    refine ⟨206299656298450323310072781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137533104198966882206715187 206299656298450323310072781)
    ·
      refine ⟨77362371111918871241277293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206299656298450323310072781 77362371111918871241277293)
      ·
        refine ⟨29010889166969576715478985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77362371111918871241277293 29010889166969576715478985)
        ·
          refine ⟨21758166875227182536609239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29010889166969576715478985 21758166875227182536609239)
          ·
            refine ⟨32637250312840773804913859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21758166875227182536609239 32637250312840773804913859)
            ·
              refine ⟨48955875469261160707370789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32637250312840773804913859 48955875469261160707370789)
              ·
                refine ⟨9179226650486467632632023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48955875469261160707370789 9179226650486467632632023)
                ·
                  refine ⟨13768839975729701448948035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9179226650486467632632023 13768839975729701448948035)
                  ·
                    refine ⟨20653259963594552173422053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13768839975729701448948035 20653259963594552173422053)
                    ·
                      refine ⟨3872486243173978532516635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20653259963594552173422053 3872486243173978532516635)
                      ·
                        rfl

theorem cell23_7541640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7541640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541640 prefixEnd_7541640 := by exact prefixLift 7541640
  have htrace : WordTrace (prefixWord ++ tailWord_7541640) baseStart_7541640 baseEnd_7541640 := by
    simpa [prefixWord, tailWord_7541640, baseEnd_7541640] using wordTrace_append hprefix tailTrace_7541640
  have hstable : (prefixWord ++ tailWord_7541640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541640).length < 2 ^ (prefixWord ++ tailWord_7541640).sum := by decide
  have hdescent : baseEnd_7541640 < baseStart_7541640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541643 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3]
def baseStart_7541643 : Nat := 118140960795 + 7541643 * 2 ^ 59
def prefixEnd_7541643 : Nat := 4983230072969 + 3 ^ 40 * 7541643 * 2
def baseEnd_7541643 : Nat := 3872487783615942020779121

theorem tailTrace_7541643 : CollatzResearch.WordTrace tailWord_7541643 prefixEnd_7541643 3872487783615942020779121 := by
  unfold tailWord_7541643
  simp only [CollatzResearch.WordTrace]
  refine ⟨275066317816922895925789583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183377545211281930617193055 275066317816922895925789583)
  ·
    refine ⟨412599476725384343888684375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275066317816922895925789583 412599476725384343888684375)
    ·
      refine ⟨618899215088076515833026563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412599476725384343888684375 618899215088076515833026563)
      ·
        refine ⟨928348822632114773749539845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618899215088076515833026563 928348822632114773749539845)
        ·
          refine ⟨174065404243521520078038721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 928348822632114773749539845 174065404243521520078038721)
          ·
            refine ⟨130549053182641140058529041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174065404243521520078038721 130549053182641140058529041)
            ·
              refine ⟨97911789886980855043896781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130549053182641140058529041 97911789886980855043896781)
              ·
                refine ⟨36716921207617820641461293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97911789886980855043896781 36716921207617820641461293)
                ·
                  refine ⟨13768845452856682740547985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36716921207617820641461293 13768845452856682740547985)
                  ·
                    refine ⟨10326634089642512055410989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13768845452856682740547985 10326634089642512055410989)
                    ·
                      refine ⟨3872487783615942020779121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10326634089642512055410989 3872487783615942020779121)
                      ·
                        rfl

theorem cell23_7541643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3].length) (baseStart_7541643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541643 prefixEnd_7541643 := by exact prefixLift 7541643
  have htrace : WordTrace (prefixWord ++ tailWord_7541643) baseStart_7541643 baseEnd_7541643 := by
    simpa [prefixWord, tailWord_7541643, baseEnd_7541643] using wordTrace_append hprefix tailTrace_7541643
  have hstable : (prefixWord ++ tailWord_7541643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541643).length < 2 ^ (prefixWord ++ tailWord_7541643).sum := by decide
  have hdescent : baseEnd_7541643 < baseStart_7541643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541654 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7541654 : Nat := 118140960795 + 7541654 * 2 ^ 59
def prefixEnd_7541654 : Nat := 4983230072969 + 3 ^ 40 * 7541654 * 2
def baseEnd_7541654 : Nat := 1290831143967713825913857

theorem tailTrace_7541654 : CollatzResearch.WordTrace tailWord_7541654 prefixEnd_7541654 1290831143967713825913857 := by
  unfold tailWord_7541654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191669938742690300277501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183377812679922029869626677 17191669938742690300277501)
  ·
    refine ⟨6446876227028508862604063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17191669938742690300277501 6446876227028508862604063)
    ·
      refine ⟨9670314340542763293906095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446876227028508862604063 9670314340542763293906095)
      ·
        refine ⟨14505471510814144940859143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670314340542763293906095 14505471510814144940859143)
        ·
          refine ⟨21758207266221217411288715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14505471510814144940859143 21758207266221217411288715)
          ·
            refine ⟨32637310899331826116933073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21758207266221217411288715 32637310899331826116933073)
            ·
              refine ⟨24477983174498869587699805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32637310899331826116933073 24477983174498869587699805)
              ·
                refine ⟨9179243690437076095387427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24477983174498869587699805 9179243690437076095387427)
                ·
                  refine ⟨13768865535655614143081141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9179243690437076095387427 13768865535655614143081141)
                  ·
                    refine ⟨1290831143967713825913857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13768865535655614143081141 1290831143967713825913857)
                    ·
                      rfl

theorem cell23_7541654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7541654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541654 prefixEnd_7541654 := by exact prefixLift 7541654
  have htrace : WordTrace (prefixWord ++ tailWord_7541654) baseStart_7541654 baseEnd_7541654 := by
    simpa [prefixWord, tailWord_7541654, baseEnd_7541654] using wordTrace_append hprefix tailTrace_7541654
  have hstable : (prefixWord ++ tailWord_7541654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541654).length < 2 ^ (prefixWord ++ tailWord_7541654).sum := by decide
  have hdescent : baseEnd_7541654 < baseStart_7541654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541663 : List Nat := [1, 1, 2, 5, 2, 3, 9]
def baseStart_7541663 : Nat := 118140960795 + 7541663 * 2 ^ 59
def prefixEnd_7541663 : Nat := 4983230072969 + 3 ^ 40 * 7541663 * 2
def baseEnd_7541663 : Nat := 47808617941099159784309

theorem tailTrace_7541663 : CollatzResearch.WordTrace tailWord_7541663 prefixEnd_7541663 47808617941099159784309 := by
  unfold tailWord_7541663
  simp only [CollatzResearch.WordTrace]
  refine ⟨275067047276850439341517643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183378031517900292894345095 275067047276850439341517643)
  ·
    refine ⟨412600570915275659012276465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275067047276850439341517643 412600570915275659012276465)
    ·
      refine ⟨309450428186456744259207349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412600570915275659012276465 309450428186456744259207349)
      ·
        refine ⟨29010977642480319774300689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309450428186456744259207349 29010977642480319774300689)
        ·
          refine ⟨21758233231860239830725517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29010977642480319774300689 21758233231860239830725517)
          ·
            refine ⟨8159337461947589936522069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21758233231860239830725517 8159337461947589936522069)
            ·
              refine ⟨47808617941099159784309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8159337461947589936522069 47808617941099159784309)
              ·
                rfl

theorem cell23_7541663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 9].length) (baseStart_7541663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541663 prefixEnd_7541663 := by exact prefixLift 7541663
  have htrace : WordTrace (prefixWord ++ tailWord_7541663) baseStart_7541663 baseEnd_7541663 := by
    simpa [prefixWord, tailWord_7541663, baseEnd_7541663] using wordTrace_append hprefix tailTrace_7541663
  have hstable : (prefixWord ++ tailWord_7541663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541663).length < 2 ^ (prefixWord ++ tailWord_7541663).sum := by decide
  have hdescent : baseEnd_7541663 < baseStart_7541663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541676 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_7541676 : Nat := 118140960795 + 7541676 * 2 ^ 59
def prefixEnd_7541676 : Nat := 4983230072969 + 3 ^ 40 * 7541676 * 2
def baseEnd_7541676 : Nat := 1290834909492513463888823

theorem tailTrace_7541676 : CollatzResearch.WordTrace tailWord_7541676 prefixEnd_7541676 1290834909492513463888823 := by
  unfold tailWord_7541676
  simp only [CollatzResearch.WordTrace]
  refine ⟨137533760712901671280870441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183378347617202228374493921 137533760712901671280870441)
  ·
    refine ⟨103150320534676253460652831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137533760712901671280870441 103150320534676253460652831)
    ·
      refine ⟨154725480802014380190979247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103150320534676253460652831 154725480802014380190979247)
      ·
        refine ⟨232088221203021570286468871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154725480802014380190979247 232088221203021570286468871)
        ·
          refine ⟨348132331804532355429703307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232088221203021570286468871 348132331804532355429703307)
          ·
            refine ⟨522198497706798533144554961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348132331804532355429703307 522198497706798533144554961)
            ·
              refine ⟨391648873280098899858416221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522198497706798533144554961 391648873280098899858416221)
              ·
                refine ⟨146868327480037087446906083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391648873280098899858416221 146868327480037087446906083)
                ·
                  refine ⟨220302491220055631170359125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146868327480037087446906083 220302491220055631170359125)
                  ·
                    refine ⟨1290834909492513463888823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220302491220055631170359125 1290834909492513463888823)
                    ·
                      rfl

theorem cell23_7541676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_7541676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541676 prefixEnd_7541676 := by exact prefixLift 7541676
  have htrace : WordTrace (prefixWord ++ tailWord_7541676) baseStart_7541676 baseEnd_7541676 := by
    simpa [prefixWord, tailWord_7541676, baseEnd_7541676] using wordTrace_append hprefix tailTrace_7541676
  have hstable : (prefixWord ++ tailWord_7541676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541676).length < 2 ^ (prefixWord ++ tailWord_7541676).sum := by decide
  have hdescent : baseEnd_7541676 < baseStart_7541676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541684 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7541684 : Nat := 118140960795 + 7541684 * 2 ^ 59
def prefixEnd_7541684 : Nat := 4983230072969 + 3 ^ 40 * 7541684 * 2
def baseEnd_7541684 : Nat := 1290836278774258786788811

theorem tailTrace_7541684 : CollatzResearch.WordTrace tailWord_7541684 prefixEnd_7541684 1290836278774258786788811 := by
  unfold tailWord_7541684
  simp only [CollatzResearch.WordTrace]
  refine ⟨137533906604887179964016053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183378542139849573285354737 137533906604887179964016053)
  ·
    refine ⟨12893803744208173121626505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137533906604887179964016053 12893803744208173121626505)
    ·
      refine ⟨9670352808156129841219879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12893803744208173121626505 9670352808156129841219879)
      ·
        refine ⟨14505529212234194761829819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670352808156129841219879 14505529212234194761829819)
        ·
          refine ⟨21758293818351292142744729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14505529212234194761829819 21758293818351292142744729)
          ·
            refine ⟨16318720363763469107058547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21758293818351292142744729 16318720363763469107058547)
            ·
              refine ⟨24478080545645203660587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16318720363763469107058547 24478080545645203660587821)
              ·
                refine ⟨9179280204616951372720433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24478080545645203660587821 9179280204616951372720433)
                ·
                  refine ⟨6884460153462713529540325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9179280204616951372720433 6884460153462713529540325)
                  ·
                    refine ⟨1290836278774258786788811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6884460153462713529540325 1290836278774258786788811)
                    ·
                      rfl

theorem cell23_7541684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7541684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541684 prefixEnd_7541684 := by exact prefixLift 7541684
  have htrace : WordTrace (prefixWord ++ tailWord_7541684) baseStart_7541684 baseEnd_7541684 := by
    simpa [prefixWord, tailWord_7541684, baseEnd_7541684] using wordTrace_append hprefix tailTrace_7541684
  have hstable : (prefixWord ++ tailWord_7541684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541684).length < 2 ^ (prefixWord ++ tailWord_7541684).sum := by decide
  have hdescent : baseEnd_7541684 < baseStart_7541684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541743 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_7541743 : Nat := 118140960795 + 7541743 * 2 ^ 59
def prefixEnd_7541743 : Nat := 4983230072969 + 3 ^ 40 * 7541743 * 2
def baseEnd_7541743 : Nat := 3872539131681391629528661

theorem tailTrace_7541743 : CollatzResearch.WordTrace tailWord_7541743 prefixEnd_7541743 3872539131681391629528661 := by
  unfold tailWord_7541743
  simp only [CollatzResearch.WordTrace]
  refine ⟨275069965116560613004429883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183379976744373742002953255 275069965116560613004429883)
  ·
    refine ⟨412604947674840919506644825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275069965116560613004429883 412604947674840919506644825)
    ·
      refine ⟨309453710756130689629983619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412604947674840919506644825 309453710756130689629983619)
      ·
        refine ⟨464180566134196034444975429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309453710756130689629983619 464180566134196034444975429)
        ·
          refine ⟨87033856150161756458432893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464180566134196034444975429 87033856150161756458432893)
          ·
            refine ⟨32637696056310658671912335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87033856150161756458432893 32637696056310658671912335)
            ·
              refine ⟨48956544084465988007868503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32637696056310658671912335 48956544084465988007868503)
              ·
                refine ⟨73434816126698982011802755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48956544084465988007868503 73434816126698982011802755)
                ·
                  refine ⟨110152224190048473017704133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73434816126698982011802755 110152224190048473017704133)
                  ·
                    refine ⟨20653542035634088690819525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110152224190048473017704133 20653542035634088690819525)
                    ·
                      refine ⟨3872539131681391629528661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20653542035634088690819525 3872539131681391629528661)
                      ·
                        rfl

theorem cell23_7541743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_7541743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541743 prefixEnd_7541743 := by exact prefixLift 7541743
  have htrace : WordTrace (prefixWord ++ tailWord_7541743) baseStart_7541743 baseEnd_7541743 := by
    simpa [prefixWord, tailWord_7541743, baseEnd_7541743] using wordTrace_append hprefix tailTrace_7541743
  have hstable : (prefixWord ++ tailWord_7541743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541743).length < 2 ^ (prefixWord ++ tailWord_7541743).sum := by decide
  have hdescent : baseEnd_7541743 < baseStart_7541743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541753 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 7]
def baseStart_7541753 : Nat := 118140960795 + 7541753 * 2 ^ 59
def prefixEnd_7541753 : Nat := 4983230072969 + 3 ^ 40 * 7541753 * 2
def baseEnd_7541753 : Nat := 430282696276437398933735

theorem tailTrace_7541753 : CollatzResearch.WordTrace tailWord_7541753 prefixEnd_7541753 430282696276437398933735 := by
  unfold tailWord_7541753
  simp only [CollatzResearch.WordTrace]
  refine ⟨275070329846524384712293913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183380219897682923141529275 275070329846524384712293913)
  ·
    refine ⟨206302747384893288534220435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275070329846524384712293913 206302747384893288534220435)
    ·
      refine ⟨309454121077339932801330653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206302747384893288534220435 309454121077339932801330653)
      ·
        refine ⟨116045295404002474800498995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309454121077339932801330653 116045295404002474800498995)
        ·
          refine ⟨174067943106003712200748493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116045295404002474800498995 174067943106003712200748493)
          ·
            refine ⟨65275478664751392075280685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174067943106003712200748493 65275478664751392075280685)
            ·
              refine ⟨24478304499281772028230257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65275478664751392075280685 24478304499281772028230257)
              ·
                refine ⟨18358728374461329021172693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24478304499281772028230257 18358728374461329021172693)
                ·
                  refine ⟨430282696276437398933735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18358728374461329021172693 430282696276437398933735)
                  ·
                    rfl

theorem cell23_7541753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_7541753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541753 prefixEnd_7541753 := by exact prefixLift 7541753
  have htrace : WordTrace (prefixWord ++ tailWord_7541753) baseStart_7541753 baseEnd_7541753 := by
    simpa [prefixWord, tailWord_7541753, baseEnd_7541753] using wordTrace_append hprefix tailTrace_7541753
  have hstable : (prefixWord ++ tailWord_7541753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541753).length < 2 ^ (prefixWord ++ tailWord_7541753).sum := by decide
  have hdescent : baseEnd_7541753 < baseStart_7541753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541781 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_7541781 : Nat := 118140960795 + 7541781 * 2 ^ 59
def prefixEnd_7541781 : Nat := 4983230072969 + 3 ^ 40 * 7541781 * 2
def baseEnd_7541781 : Nat := 3872558643946262480853487

theorem tailTrace_7541781 : CollatzResearch.WordTrace tailWord_7541781 prefixEnd_7541781 3872558643946262480853487 := by
  unfold tailWord_7541781
  simp only [CollatzResearch.WordTrace]
  refine ⟨275071351090422945494313197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183380900726948630329542131 275071351090422945494313197)
  ·
    refine ⟨103151756658908604560367449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275071351090422945494313197 103151756658908604560367449)
    ·
      refine ⟨77363817494181453420275587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103151756658908604560367449 77363817494181453420275587)
      ·
        refine ⟨116045726241272180130413381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77363817494181453420275587 116045726241272180130413381)
        ·
          refine ⟨21758573670238533774452509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116045726241272180130413381 21758573670238533774452509)
          ·
            refine ⟨8159465126339450165419691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21758573670238533774452509 8159465126339450165419691)
            ·
              refine ⟨12239197689509175248129537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8159465126339450165419691 12239197689509175248129537)
              ·
                refine ⟨9179398267131881436097153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12239197689509175248129537 9179398267131881436097153)
                ·
                  refine ⟨6884548700348911077072865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9179398267131881436097153 6884548700348911077072865)
                  ·
                    refine ⟨5163411525261683307804649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6884548700348911077072865 5163411525261683307804649)
                    ·
                      refine ⟨3872558643946262480853487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5163411525261683307804649 3872558643946262480853487)
                      ·
                        rfl

theorem cell23_7541781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_7541781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541781 prefixEnd_7541781 := by exact prefixLift 7541781
  have htrace : WordTrace (prefixWord ++ tailWord_7541781) baseStart_7541781 baseEnd_7541781 := by
    simpa [prefixWord, tailWord_7541781, baseEnd_7541781] using wordTrace_append hprefix tailTrace_7541781
  have hstable : (prefixWord ++ tailWord_7541781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541781).length < 2 ^ (prefixWord ++ tailWord_7541781).sum := by decide
  have hdescent : baseEnd_7541781 < baseStart_7541781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541803 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_7541803 : Nat := 118140960795 + 7541803 * 2 ^ 59
def prefixEnd_7541803 : Nat := 4983230072969 + 3 ^ 40 * 7541803 * 2
def baseEnd_7541803 : Nat := 3872569940520661394778385

theorem tailTrace_7541803 : CollatzResearch.WordTrace tailWord_7541803 prefixEnd_7541803 3872569940520661394778385 := by
  unfold tailWord_7541803
  simp only [CollatzResearch.WordTrace]
  refine ⟨275072153496343243251614063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183381435664228828834409375 275072153496343243251614063)
  ·
    refine ⟨412608230244514864877421095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275072153496343243251614063 412608230244514864877421095)
    ·
      refine ⟨618912345366772297316131643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412608230244514864877421095 618912345366772297316131643)
      ·
        refine ⟨928368518050158445974197465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618912345366772297316131643 928368518050158445974197465)
        ·
          refine ⟨696276388537618834480648099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928368518050158445974197465 696276388537618834480648099)
          ·
            refine ⟨1044414582806428251720972149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696276388537618834480648099 1044414582806428251720972149)
            ·
              refine ⟨97913867138102648598841139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1044414582806428251720972149 97913867138102648598841139)
              ·
                refine ⟨146870800707153972898261709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97913867138102648598841139 146870800707153972898261709)
                ·
                  refine ⟨55076550265182739836848141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146870800707153972898261709 55076550265182739836848141)
                  ·
                    refine ⟨20653706349443527438818053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55076550265182739836848141 20653706349443527438818053)
                    ·
                      refine ⟨3872569940520661394778385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20653706349443527438818053 3872569940520661394778385)
                      ·
                        rfl

theorem cell23_7541803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_7541803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541803 prefixEnd_7541803 := by exact prefixLift 7541803
  have htrace : WordTrace (prefixWord ++ tailWord_7541803) baseStart_7541803 baseEnd_7541803 := by
    simpa [prefixWord, tailWord_7541803, baseEnd_7541803] using wordTrace_append hprefix tailTrace_7541803
  have hstable : (prefixWord ++ tailWord_7541803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541803).length < 2 ^ (prefixWord ++ tailWord_7541803).sum := by decide
  have hdescent : baseEnd_7541803 < baseStart_7541803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541813 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7541813 : Nat := 118140960795 + 7541813 * 2 ^ 59
def prefixEnd_7541813 : Nat := 4983230072969 + 3 ^ 40 * 7541813 * 2
def baseEnd_7541813 : Nat := 1290858358442402118551113

theorem tailTrace_7541813 : CollatzResearch.WordTrace tailWord_7541813 prefixEnd_7541813 1290858358442402118551113 := by
  unfold tailWord_7541813
  simp only [CollatzResearch.WordTrace]
  refine ⟨275072518226307014959478093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183381678817538009972985395 275072518226307014959478093)
  ·
    refine ⟨103152194334865130609804285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275072518226307014959478093 103152194334865130609804285)
    ·
      refine ⟨38682072875574423978676607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103152194334865130609804285 38682072875574423978676607)
      ·
        refine ⟨58023109313361635968014911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38682072875574423978676607 58023109313361635968014911)
        ·
          refine ⟨87034663970042453952022367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58023109313361635968014911 87034663970042453952022367)
          ·
            refine ⟨130551995955063680928033551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87034663970042453952022367 130551995955063680928033551)
            ·
              refine ⟨195827993932595521392050327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130551995955063680928033551 195827993932595521392050327)
              ·
                refine ⟨293741990898893282088075491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195827993932595521392050327 293741990898893282088075491)
                ·
                  refine ⟨440612986348339923132113237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293741990898893282088075491 440612986348339923132113237)
                  ·
                    refine ⟨1290858358442402118551113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 440612986348339923132113237 1290858358442402118551113)
                    ·
                      rfl

theorem cell23_7541813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7541813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541813 prefixEnd_7541813 := by exact prefixLift 7541813
  have htrace : WordTrace (prefixWord ++ tailWord_7541813) baseStart_7541813 baseEnd_7541813 := by
    simpa [prefixWord, tailWord_7541813, baseEnd_7541813] using wordTrace_append hprefix tailTrace_7541813
  have hstable : (prefixWord ++ tailWord_7541813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541813).length < 2 ^ (prefixWord ++ tailWord_7541813).sum := by decide
  have hdescent : baseEnd_7541813 < baseStart_7541813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541820 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7541820 : Nat := 118140960795 + 7541820 * 2 ^ 59
def prefixEnd_7541820 : Nat := 4983230072969 + 3 ^ 40 * 7541820 * 2
def baseEnd_7541820 : Nat := 3872578669691787828265807

theorem tailTrace_7541820 : CollatzResearch.WordTrace tailWord_7541820 prefixEnd_7541820 3872578669691787828265807 := by
  unfold tailWord_7541820
  simp only [CollatzResearch.WordTrace]
  refine ⟨137536386768640827577491457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183381849024854436769988609 137536386768640827577491457)
  ·
    refine ⟨103152290076480620683118593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137536386768640827577491457 103152290076480620683118593)
    ·
      refine ⟨77364217557360465512338945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103152290076480620683118593 77364217557360465512338945)
      ·
        refine ⟨58023163168020349134254209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77364217557360465512338945 58023163168020349134254209)
        ·
          refine ⟨43517372376015261850690657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58023163168020349134254209 43517372376015261850690657)
          ·
            refine ⟨32638029282011446388017993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43517372376015261850690657 32638029282011446388017993)
            ·
              refine ⟨24478521961508584791013495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32638029282011446388017993 24478521961508584791013495)
              ·
                refine ⟨36717782942262877186520243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24478521961508584791013495 36717782942262877186520243)
                ·
                  refine ⟨55076674413394315779780365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36717782942262877186520243 55076674413394315779780365)
                  ·
                    refine ⟨20653752905022868417417637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55076674413394315779780365 20653752905022868417417637)
                    ·
                      refine ⟨3872578669691787828265807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20653752905022868417417637 3872578669691787828265807)
                      ·
                        rfl

theorem cell23_7541820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7541820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541820 prefixEnd_7541820 := by exact prefixLift 7541820
  have htrace : WordTrace (prefixWord ++ tailWord_7541820) baseStart_7541820 baseEnd_7541820 := by
    simpa [prefixWord, tailWord_7541820, baseEnd_7541820] using wordTrace_append hprefix tailTrace_7541820
  have hstable : (prefixWord ++ tailWord_7541820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541820).length < 2 ^ (prefixWord ++ tailWord_7541820).sum := by decide
  have hdescent : baseEnd_7541820 < baseStart_7541820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541823 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_7541823 : Nat := 118140960795 + 7541823 * 2 ^ 59
def prefixEnd_7541823 : Nat := 4983230072969 + 3 ^ 40 * 7541823 * 2
def baseEnd_7541823 : Nat := 3872580210133751316528293

theorem tailTrace_7541823 : CollatzResearch.WordTrace tailWord_7541823 prefixEnd_7541823 3872580210133751316528293 := by
  unfold tailWord_7541823
  simp only [CollatzResearch.WordTrace]
  refine ⟨275072882956270786667342123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183381921970847191111561415 275072882956270786667342123)
  ·
    refine ⟨412609324434406180001013185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275072882956270786667342123 412609324434406180001013185)
    ·
      refine ⟨309456993325804635000759889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412609324434406180001013185 309456993325804635000759889)
      ·
        refine ⟨232092744994353476250569917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309456993325804635000759889 232092744994353476250569917)
        ·
          refine ⟨87034779372882553593963719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232092744994353476250569917 87034779372882553593963719)
          ·
            refine ⟨130552169059323830390945579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87034779372882553593963719 130552169059323830390945579)
            ·
              refine ⟨195828253588985745586418369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130552169059323830390945579 195828253588985745586418369)
              ·
                refine ⟨146871190191739309189813777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195828253588985745586418369 146871190191739309189813777)
                ·
                  refine ⟨110153392643804481892360333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146871190191739309189813777 110153392643804481892360333)
                  ·
                    refine ⟨41307522241426680709635125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110153392643804481892360333 41307522241426680709635125)
                    ·
                      refine ⟨3872580210133751316528293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41307522241426680709635125 3872580210133751316528293)
                      ·
                        rfl

theorem cell23_7541823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_7541823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541823 prefixEnd_7541823 := by exact prefixLift 7541823
  have htrace : WordTrace (prefixWord ++ tailWord_7541823) baseStart_7541823 baseEnd_7541823 := by
    simpa [prefixWord, tailWord_7541823, baseEnd_7541823] using wordTrace_append hprefix tailTrace_7541823
  have hstable : (prefixWord ++ tailWord_7541823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541823).length < 2 ^ (prefixWord ++ tailWord_7541823).sum := by decide
  have hdescent : baseEnd_7541823 < baseStart_7541823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7541833 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_7541833 : Nat := 118140960795 + 7541833 * 2 ^ 59
def prefixEnd_7541833 : Nat := 4983230072969 + 3 ^ 40 * 7541833 * 2
def baseEnd_7541833 : Nat := 3872585344940296277403247

theorem tailTrace_7541833 : CollatzResearch.WordTrace tailWord_7541833 prefixEnd_7541833 3872585344940296277403247 := by
  unfold tailWord_7541833
  simp only [CollatzResearch.WordTrace]
  refine ⟨275073247686234558375206153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183382165124156372250137435 275073247686234558375206153)
  ·
    refine ⟨206304935764675918781404615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275073247686234558375206153 206304935764675918781404615)
    ·
      refine ⟨309457403647013878172106923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206304935764675918781404615 309457403647013878172106923)
      ·
        refine ⟨464186105470520817258160385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309457403647013878172106923 464186105470520817258160385)
        ·
          refine ⟨348139579102890612943620289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464186105470520817258160385 348139579102890612943620289)
          ·
            refine ⟨261104684327167959707715217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348139579102890612943620289 261104684327167959707715217)
            ·
              refine ⟨195828513245375969780786413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261104684327167959707715217 195828513245375969780786413)
              ·
                refine ⟨73435692467015988667794905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195828513245375969780786413 73435692467015988667794905)
                ·
                  refine ⟨55076769350261991500846179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73435692467015988667794905 55076769350261991500846179)
                  ·
                    refine ⟨82615154025392987251269269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55076769350261991500846179 82615154025392987251269269)
                    ·
                      refine ⟨3872585344940296277403247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82615154025392987251269269 3872585344940296277403247)
                      ·
                        rfl

theorem cell23_7541833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_7541833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7541833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7541833 prefixEnd_7541833 := by exact prefixLift 7541833
  have htrace : WordTrace (prefixWord ++ tailWord_7541833) baseStart_7541833 baseEnd_7541833 := by
    simpa [prefixWord, tailWord_7541833, baseEnd_7541833] using wordTrace_append hprefix tailTrace_7541833
  have hstable : (prefixWord ++ tailWord_7541833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7541833).length < 2 ^ (prefixWord ++ tailWord_7541833).sum := by decide
  have hdescent : baseEnd_7541833 < baseStart_7541833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7541833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
