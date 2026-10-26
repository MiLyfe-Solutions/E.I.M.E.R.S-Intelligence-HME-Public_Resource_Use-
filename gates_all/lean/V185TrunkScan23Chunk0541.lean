import V185TrunkScan23Chunk0540

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3199056 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_3199056 : Nat := 118140960795 + 3199056 * 2 ^ 59
def prefixEnd_3199056 : Nat := 4983230072969 + 3 ^ 40 * 3199056 * 2
def baseEnd_3199056 : Nat := 1642653368649740912387815

theorem tailTrace_3199056 : CollatzResearch.WordTrace tailWord_3199056 prefixEnd_3199056 1642653368649740912387815 := by
  unfold tailWord_3199056
  simp only [CollatzResearch.WordTrace]
  refine ⟨58339578949186971056172511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77786105265582628074896681 58339578949186971056172511)
  ·
    refine ⟨87509368423780456584258767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58339578949186971056172511 87509368423780456584258767)
    ·
      refine ⟨131264052635670684876388151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87509368423780456584258767 131264052635670684876388151)
      ·
        refine ⟨196896078953506027314582227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131264052635670684876388151 196896078953506027314582227)
        ·
          refine ⟨295344118430259040971873341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196896078953506027314582227 295344118430259040971873341)
          ·
            refine ⟨110754044411347140364452503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295344118430259040971873341 110754044411347140364452503)
            ·
              refine ⟨166131066617020710546678755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110754044411347140364452503 166131066617020710546678755)
              ·
                refine ⟨249196599925531065820018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166131066617020710546678755 249196599925531065820018133)
                ·
                  refine ⟨5840545310754634355156675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249196599925531065820018133 5840545310754634355156675)
                  ·
                    refine ⟨8760817966131951532735013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840545310754634355156675 8760817966131951532735013)
                    ·
                      refine ⟨1642653368649740912387815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8760817966131951532735013 1642653368649740912387815)
                      ·
                        rfl

theorem cell23_3199056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_3199056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199056 prefixEnd_3199056 := by exact prefixLift 3199056
  have htrace : WordTrace (prefixWord ++ tailWord_3199056) baseStart_3199056 baseEnd_3199056 := by
    simpa [prefixWord, tailWord_3199056, baseEnd_3199056] using wordTrace_append hprefix tailTrace_3199056
  have hstable : (prefixWord ++ tailWord_3199056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199056).length < 2 ^ (prefixWord ++ tailWord_3199056).sum := by decide
  have hdescent : baseEnd_3199056 < baseStart_3199056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199074 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_3199074 : Nat := 118140960795 + 3199074 * 2 ^ 59
def prefixEnd_3199074 : Nat := 4983230072969 + 3 ^ 40 * 3199074 * 2
def baseEnd_3199074 : Nat := 182518067922391315773637

theorem tailTrace_3199074 : CollatzResearch.WordTrace tailWord_3199074 prefixEnd_3199074 182518067922391315773637 := by
  unfold tailWord_3199074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169953603077182796625069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77786542941539154124333517 29169953603077182796625069)
  ·
    refine ⟨10938732601153943548734401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29169953603077182796625069 10938732601153943548734401)
    ·
      refine ⟨8204049450865457661550801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10938732601153943548734401 8204049450865457661550801)
      ·
        refine ⟨6153037088149093246163101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8204049450865457661550801 6153037088149093246163101)
        ·
          refine ⟨2307388908055909967311163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6153037088149093246163101 2307388908055909967311163)
          ·
            refine ⟨3461083362083864950966745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307388908055909967311163 3461083362083864950966745)
            ·
              refine ⟨2595812521562898713225059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461083362083864950966745 2595812521562898713225059)
              ·
                refine ⟨3893718782344348069837589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595812521562898713225059 3893718782344348069837589)
                ·
                  refine ⟨182518067922391315773637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3893718782344348069837589 182518067922391315773637)
                  ·
                    rfl

theorem cell23_3199074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_3199074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199074 prefixEnd_3199074 := by exact prefixLift 3199074
  have htrace : WordTrace (prefixWord ++ tailWord_3199074) baseStart_3199074 baseEnd_3199074 := by
    simpa [prefixWord, tailWord_3199074, baseEnd_3199074] using wordTrace_append hprefix tailTrace_3199074
  have hstable : (prefixWord ++ tailWord_3199074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199074).length < 2 ^ (prefixWord ++ tailWord_3199074).sum := by decide
  have hdescent : baseEnd_3199074 < baseStart_3199074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199090 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3199090 : Nat := 118140960795 + 3199090 * 2 ^ 59
def prefixEnd_3199090 : Nat := 4983230072969 + 3 ^ 40 * 3199090 * 2
def baseEnd_3199090 : Nat := 1642670826991993779362659

theorem tailTrace_3199090 : CollatzResearch.WordTrace tailWord_3199090 prefixEnd_3199090 1642670826991993779362659 := by
  unfold tailWord_3199090
  simp only [CollatzResearch.WordTrace]
  refine ⟨29170099495062691479770681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77786931986833843946055149 29170099495062691479770681)
  ·
    refine ⟨21877574621297018609828011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29170099495062691479770681 21877574621297018609828011)
    ·
      refine ⟨32816361931945527914742017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21877574621297018609828011 32816361931945527914742017)
      ·
        refine ⟨24612271448959145936056513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32816361931945527914742017 24612271448959145936056513)
        ·
          refine ⟨18459203586719359452042385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24612271448959145936056513 18459203586719359452042385)
          ·
            refine ⟨13844402690039519589031789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18459203586719359452042385 13844402690039519589031789)
            ·
              refine ⟨5191651008764819845886921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13844402690039519589031789 5191651008764819845886921)
              ·
                refine ⟨3893738256573614884415191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191651008764819845886921 3893738256573614884415191)
                ·
                  refine ⟨5840607384860422326622787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893738256573614884415191 5840607384860422326622787)
                  ·
                    refine ⟨8760911077290633489934181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840607384860422326622787 8760911077290633489934181)
                    ·
                      refine ⟨1642670826991993779362659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8760911077290633489934181 1642670826991993779362659)
                      ·
                        rfl

theorem cell23_3199090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3199090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199090 prefixEnd_3199090 := by exact prefixLift 3199090
  have htrace : WordTrace (prefixWord ++ tailWord_3199090) baseStart_3199090 baseEnd_3199090 := by
    simpa [prefixWord, tailWord_3199090, baseEnd_3199090] using wordTrace_append hprefix tailTrace_3199090
  have hstable : (prefixWord ++ tailWord_3199090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199090).length < 2 ^ (prefixWord ++ tailWord_3199090).sum := by decide
  have hdescent : baseEnd_3199090 < baseStart_3199090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199118 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3199118 : Nat := 118140960795 + 3199118 * 2 ^ 59
def prefixEnd_3199118 : Nat := 4983230072969 + 3 ^ 40 * 3199118 * 2
def baseEnd_3199118 : Nat := 1642685204450319669812531

theorem tailTrace_3199118 : CollatzResearch.WordTrace tailWord_3199118 prefixEnd_3199118 1642685204450319669812531 := by
  unfold tailWord_3199118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14585177403018665837637751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77787612816099551134068005 14585177403018665837637751)
  ·
    refine ⟨21877766104527998756456627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14585177403018665837637751 21877766104527998756456627)
    ·
      refine ⟨32816649156791998134684941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21877766104527998756456627 32816649156791998134684941)
      ·
        refine ⟨12306243433796999300506853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32816649156791998134684941 12306243433796999300506853)
        ·
          refine ⟨2307420643836937368845035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12306243433796999300506853 2307420643836937368845035)
          ·
            refine ⟨3461130965755406053267553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307420643836937368845035 3461130965755406053267553)
            ·
              refine ⟨2595848224316554539950665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461130965755406053267553 2595848224316554539950665)
              ·
                refine ⟨1946886168237415904962999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595848224316554539950665 1946886168237415904962999)
                ·
                  refine ⟨2920329252356123857444499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946886168237415904962999 2920329252356123857444499)
                  ·
                    refine ⟨4380493878534185786166749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2920329252356123857444499 4380493878534185786166749)
                    ·
                      refine ⟨1642685204450319669812531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380493878534185786166749 1642685204450319669812531)
                      ·
                        rfl

theorem cell23_3199118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3199118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199118 prefixEnd_3199118 := by exact prefixLift 3199118
  have htrace : WordTrace (prefixWord ++ tailWord_3199118) baseStart_3199118 baseEnd_3199118 := by
    simpa [prefixWord, tailWord_3199118, baseEnd_3199118] using wordTrace_append hprefix tailTrace_3199118
  have hstable : (prefixWord ++ tailWord_3199118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199118).length < 2 ^ (prefixWord ++ tailWord_3199118).sum := by decide
  have hdescent : baseEnd_3199118 < baseStart_3199118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199130 : List Nat := [3, 1, 1, 5, 2, 2, 1, 8]
def baseStart_3199130 : Nat := 118140960795 + 3199130 * 2 ^ 59
def prefixEnd_3199130 : Nat := 4983230072969 + 3 ^ 40 * 3199130 * 2
def baseEnd_3199130 : Nat := 60840420971043467513425

theorem tailTrace_3199130 : CollatzResearch.WordTrace tailWord_3199130 prefixEnd_3199130 60840420971043467513425 := by
  unfold tailWord_3199130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29170464225026463187634711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77787904600070568500359229 29170464225026463187634711)
  ·
    refine ⟨43755696337539694781452067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29170464225026463187634711 43755696337539694781452067)
    ·
      refine ⟨65633544506309542172178101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43755696337539694781452067 65633544506309542172178101)
      ·
        refine ⟨6153144797466519578641697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65633544506309542172178101 6153144797466519578641697)
        ·
          refine ⟨4614858598099889683981273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6153144797466519578641697 4614858598099889683981273)
          ·
            refine ⟨3461143948574917262985955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4614858598099889683981273 3461143948574917262985955)
            ·
              refine ⟨5191715922862375894478933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461143948574917262985955 5191715922862375894478933)
              ·
                refine ⟨60840420971043467513425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5191715922862375894478933 60840420971043467513425)
                ·
                  rfl

theorem cell23_3199130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_3199130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199130 prefixEnd_3199130 := by exact prefixLift 3199130
  have htrace : WordTrace (prefixWord ++ tailWord_3199130) baseStart_3199130 baseEnd_3199130 := by
    simpa [prefixWord, tailWord_3199130, baseEnd_3199130] using wordTrace_append hprefix tailTrace_3199130
  have hstable : (prefixWord ++ tailWord_3199130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199130).length < 2 ^ (prefixWord ++ tailWord_3199130).sum := by decide
  have hdescent : baseEnd_3199130 < baseStart_3199130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199193 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3199193 : Nat := 118140960795 + 3199193 * 2 ^ 59
def prefixEnd_3199193 : Nat := 4983230072969 + 3 ^ 40 * 3199193 * 2
def baseEnd_3199193 : Nat := 1642723715499406876374685

theorem tailTrace_3199193 : CollatzResearch.WordTrace tailWord_3199193 prefixEnd_3199193 1642723715499406876374685 := by
  unfold tailWord_3199193
  simp only [CollatzResearch.WordTrace]
  refine ⟨116684154698877614510082233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77789436465918409673388155 116684154698877614510082233)
  ·
    refine ⟨87513116024158210882561675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116684154698877614510082233 87513116024158210882561675)
    ·
      refine ⟨131269674036237316323842513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87513116024158210882561675 131269674036237316323842513)
      ·
        refine ⟨98452255527177987242881885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131269674036237316323842513 98452255527177987242881885)
        ·
          refine ⟨36919595822691745216080707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98452255527177987242881885 36919595822691745216080707)
          ·
            refine ⟨55379393734037617824121061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36919595822691745216080707 55379393734037617824121061)
            ·
              refine ⟨10383636325132053342022699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55379393734037617824121061 10383636325132053342022699)
              ·
                refine ⟨15575454487698080013034049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383636325132053342022699 15575454487698080013034049)
                ·
                  refine ⟨11681590865773560009775537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15575454487698080013034049 11681590865773560009775537)
                  ·
                    refine ⟨8761193149330170007331653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11681590865773560009775537 8761193149330170007331653)
                    ·
                      refine ⟨1642723715499406876374685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8761193149330170007331653 1642723715499406876374685)
                      ·
                        rfl

theorem cell23_3199193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3199193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199193 prefixEnd_3199193 := by exact prefixLift 3199193
  have htrace : WordTrace (prefixWord ++ tailWord_3199193) baseStart_3199193 baseEnd_3199193 := by
    simpa [prefixWord, tailWord_3199193, baseEnd_3199193] using wordTrace_append hprefix tailTrace_3199193
  have hstable : (prefixWord ++ tailWord_3199193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199193).length < 2 ^ (prefixWord ++ tailWord_3199193).sum := by decide
  have hdescent : baseEnd_3199193 < baseStart_3199193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199243 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_3199243 : Nat := 118140960795 + 3199243 * 2 ^ 59
def prefixEnd_3199243 : Nat := 4983230072969 + 3 ^ 40 * 3199243 * 2
def baseEnd_3199243 : Nat := 1642749389532131680749455

theorem tailTrace_3199243 : CollatzResearch.WordTrace tailWord_3199243 prefixEnd_3199243 1642749389532131680749455 := by
  unfold tailWord_3199243
  simp only [CollatzResearch.WordTrace]
  refine ⟨116685978348696473049402383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77790652232464315366268255 116685978348696473049402383)
  ·
    refine ⟨175028967523044709574103575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116685978348696473049402383 175028967523044709574103575)
    ·
      refine ⟨262543451284567064361155363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175028967523044709574103575 262543451284567064361155363)
      ·
        refine ⟨393815176926850596541733045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262543451284567064361155363 393815176926850596541733045)
        ·
          refine ⟨36920172836892243425787473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 393815176926850596541733045 36920172836892243425787473)
          ·
            refine ⟨27690129627669182569340605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36920172836892243425787473 27690129627669182569340605)
            ·
              refine ⟨10383798610375943463502727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27690129627669182569340605 10383798610375943463502727)
              ·
                refine ⟨15575697915563915195254091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383798610375943463502727 15575697915563915195254091)
                ·
                  refine ⟨23363546873345872792881137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15575697915563915195254091 23363546873345872792881137)
                  ·
                    refine ⟨17522660155009404594660853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23363546873345872792881137 17522660155009404594660853)
                    ·
                      refine ⟨1642749389532131680749455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17522660155009404594660853 1642749389532131680749455)
                      ·
                        rfl

theorem cell23_3199243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_3199243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199243 prefixEnd_3199243 := by exact prefixLift 3199243
  have htrace : WordTrace (prefixWord ++ tailWord_3199243) baseStart_3199243 baseEnd_3199243 := by
    simpa [prefixWord, tailWord_3199243, baseEnd_3199243] using wordTrace_append hprefix tailTrace_3199243
  have hstable : (prefixWord ++ tailWord_3199243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199243).length < 2 ^ (prefixWord ++ tailWord_3199243).sum := by decide
  have hdescent : baseEnd_3199243 < baseStart_3199243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199253 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3199253 : Nat := 118140960795 + 3199253 * 2 ^ 59
def prefixEnd_3199253 : Nat := 4983230072969 + 3 ^ 40 * 3199253 * 2
def baseEnd_3199253 : Nat := 1642754524338676641624409

theorem tailTrace_3199253 : CollatzResearch.WordTrace tailWord_3199253 prefixEnd_3199253 1642754524338676641624409 := by
  unfold tailWord_3199253
  simp only [CollatzResearch.WordTrace]
  refine ⟨116686343078660244757266413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77790895385773496504844275 116686343078660244757266413)
  ·
    refine ⟨43757378654497591783974905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116686343078660244757266413 43757378654497591783974905)
    ·
      refine ⟨32818033990873193837981179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43757378654497591783974905 32818033990873193837981179)
      ·
        refine ⟨49227050986309790756971769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32818033990873193837981179 49227050986309790756971769)
        ·
          refine ⟨36920288239732343067728827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49227050986309790756971769 36920288239732343067728827)
          ·
            refine ⟨55380432359598514601593241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36920288239732343067728827 55380432359598514601593241)
            ·
              refine ⟨41535324269698885951194931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55380432359598514601593241 41535324269698885951194931)
              ·
                refine ⟨62302986404548328926792397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41535324269698885951194931 62302986404548328926792397)
                ·
                  refine ⟨23363619901705623347547149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62302986404548328926792397 23363619901705623347547149)
                  ·
                    refine ⟨8761357463139608755330181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23363619901705623347547149 8761357463139608755330181)
                    ·
                      refine ⟨1642754524338676641624409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8761357463139608755330181 1642754524338676641624409)
                      ·
                        rfl

theorem cell23_3199253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3199253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199253 prefixEnd_3199253 := by exact prefixLift 3199253
  have htrace : WordTrace (prefixWord ++ tailWord_3199253) baseStart_3199253 baseEnd_3199253 := by
    simpa [prefixWord, tailWord_3199253, baseEnd_3199253] using wordTrace_append hprefix tailTrace_3199253
  have hstable : (prefixWord ++ tailWord_3199253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199253).length < 2 ^ (prefixWord ++ tailWord_3199253).sum := by decide
  have hdescent : baseEnd_3199253 < baseStart_3199253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199283 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_3199283 : Nat := 118140960795 + 3199283 * 2 ^ 59
def prefixEnd_3199283 : Nat := 4983230072969 + 3 ^ 40 * 3199283 * 2
def baseEnd_3199283 : Nat := 1642769928758311524249271

theorem tailTrace_3199283 : CollatzResearch.WordTrace tailWord_3199283 prefixEnd_3199283 1642769928758311524249271 := by
  unfold tailWord_3199283
  simp only [CollatzResearch.WordTrace]
  refine ⟨116687437268551559880858503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77791624845701039920572335 116687437268551559880858503)
  ·
    refine ⟨175031155902827339821287755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116687437268551559880858503 175031155902827339821287755)
    ·
      refine ⟨262546733854241009731931633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175031155902827339821287755 262546733854241009731931633)
      ·
        refine ⟨196910050390680757298948725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262546733854241009731931633 196910050390680757298948725)
        ·
          refine ⟨18460317224126320996776443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196910050390680757298948725 18460317224126320996776443)
          ·
            refine ⟨27690475836189481495164665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18460317224126320996776443 27690475836189481495164665)
            ·
              refine ⟨20767856877142111121373499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27690475836189481495164665 20767856877142111121373499)
              ·
                refine ⟨31151785315713166682060249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20767856877142111121373499 31151785315713166682060249)
                ·
                  refine ⟨23363838986784875011545187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31151785315713166682060249 23363838986784875011545187)
                  ·
                    refine ⟨35045758480177312517317781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23363838986784875011545187 35045758480177312517317781)
                    ·
                      refine ⟨1642769928758311524249271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35045758480177312517317781 1642769928758311524249271)
                      ·
                        rfl

theorem cell23_3199283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_3199283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199283 prefixEnd_3199283 := by exact prefixLift 3199283
  have htrace : WordTrace (prefixWord ++ tailWord_3199283) baseStart_3199283 baseEnd_3199283 := by
    simpa [prefixWord, tailWord_3199283, baseEnd_3199283] using wordTrace_append hprefix tailTrace_3199283
  have hstable : (prefixWord ++ tailWord_3199283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199283).length < 2 ^ (prefixWord ++ tailWord_3199283).sum := by decide
  have hdescent : baseEnd_3199283 < baseStart_3199283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199324 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3199324 : Nat := 118140960795 + 3199324 * 2 ^ 59
def prefixEnd_3199324 : Nat := 4983230072969 + 3 ^ 40 * 3199324 * 2
def baseEnd_3199324 : Nat := 1642790981465145863836583

theorem tailTrace_3199324 : CollatzResearch.WordTrace tailWord_3199324 prefixEnd_3199324 1642790981465145863836583 := by
  unfold tailWord_3199324
  simp only [CollatzResearch.WordTrace]
  refine ⟨58344466330701511941550513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77792621774268682588734017 58344466330701511941550513)
  ·
    refine ⟨43758349748026133956162885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58344466330701511941550513 43758349748026133956162885)
    ·
      refine ⟨8204690577754900116780541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43758349748026133956162885 8204690577754900116780541)
      ·
        refine ⟨3076758966658087543792703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8204690577754900116780541 3076758966658087543792703)
        ·
          refine ⟨4615138449987131315689055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076758966658087543792703 4615138449987131315689055)
          ·
            refine ⟨6922707674980696973533583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615138449987131315689055 6922707674980696973533583)
            ·
              refine ⟨10384061512471045460300375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6922707674980696973533583 10384061512471045460300375)
              ·
                refine ⟨15576092268706568190450563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10384061512471045460300375 15576092268706568190450563)
                ·
                  refine ⟨23364138403059852285675845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15576092268706568190450563 23364138403059852285675845)
                  ·
                    refine ⟨4380775950573722303564221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23364138403059852285675845 4380775950573722303564221)
                    ·
                      refine ⟨1642790981465145863836583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380775950573722303564221 1642790981465145863836583)
                      ·
                        rfl

theorem cell23_3199324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3199324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199324 prefixEnd_3199324 := by exact prefixLift 3199324
  have htrace : WordTrace (prefixWord ++ tailWord_3199324) baseStart_3199324 baseEnd_3199324 := by
    simpa [prefixWord, tailWord_3199324, baseEnd_3199324] using wordTrace_append hprefix tailTrace_3199324
  have hstable : (prefixWord ++ tailWord_3199324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199324).length < 2 ^ (prefixWord ++ tailWord_3199324).sum := by decide
  have hdescent : baseEnd_3199324 < baseStart_3199324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199374 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3199374 : Nat := 118140960795 + 3199374 * 2 ^ 59
def prefixEnd_3199374 : Nat := 4983230072969 + 3 ^ 40 * 3199374 * 2
def baseEnd_3199374 : Nat := 547605551832623556070451

theorem tailTrace_3199374 : CollatzResearch.WordTrace tailWord_3199374 prefixEnd_3199374 547605551832623556070451 := by
  unfold tailWord_3199374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14586344538902735302802647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77793837540814588281614117 14586344538902735302802647)
  ·
    refine ⟨21879516808354102954203971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14586344538902735302802647 21879516808354102954203971)
    ·
      refine ⟨32819275212531154431305957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21879516808354102954203971 32819275212531154431305957)
      ·
        refine ⟨6153614102349591455869867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32819275212531154431305957 6153614102349591455869867)
        ·
          refine ⟨9230421153524387183804801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153614102349591455869867 9230421153524387183804801)
          ·
            refine ⟨6922815865143290387853601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9230421153524387183804801 6922815865143290387853601)
            ·
              refine ⟨5192111898857467790890201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6922815865143290387853601 5192111898857467790890201)
              ·
                refine ⟨3894083924143100843167651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192111898857467790890201 3894083924143100843167651)
                ·
                  refine ⟨5841125886214651264751477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894083924143100843167651 5841125886214651264751477)
                  ·
                    refine ⟨547605551832623556070451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5841125886214651264751477 547605551832623556070451)
                    ·
                      rfl

theorem cell23_3199374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3199374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199374 prefixEnd_3199374 := by exact prefixLift 3199374
  have htrace : WordTrace (prefixWord ++ tailWord_3199374) baseStart_3199374 baseEnd_3199374 := by
    simpa [prefixWord, tailWord_3199374, baseEnd_3199374] using wordTrace_append hprefix tailTrace_3199374
  have hstable : (prefixWord ++ tailWord_3199374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199374).length < 2 ^ (prefixWord ++ tailWord_3199374).sum := by decide
  have hdescent : baseEnd_3199374 < baseStart_3199374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199382 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3199382 : Nat := 118140960795 + 3199382 * 2 ^ 59
def prefixEnd_3199382 : Nat := 4983230072969 + 3 ^ 40 * 3199382 * 2
def baseEnd_3199382 : Nat := 547606921114368878970439

theorem tailTrace_3199382 : CollatzResearch.WordTrace tailWord_3199382 prefixEnd_3199382 547606921114368878970439 := by
  unfold tailWord_3199382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7293190505949556236794525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77794032063461933192474933 7293190505949556236794525)
  ·
    refine ⟨2734946439731083588797947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7293190505949556236794525 2734946439731083588797947)
    ·
      refine ⟨4102419659596625383196921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734946439731083588797947 4102419659596625383196921)
      ·
        refine ⟨3076814744697469037397691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102419659596625383196921 3076814744697469037397691)
        ·
          refine ⟨4615222117046203556096537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076814744697469037397691 4615222117046203556096537)
          ·
            refine ⟨3461416587784652667072403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4615222117046203556096537 3461416587784652667072403)
            ·
              refine ⟨5192124881676979000608605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461416587784652667072403 5192124881676979000608605)
              ·
                refine ⟨1947046830628867125228227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5192124881676979000608605 1947046830628867125228227)
                ·
                  refine ⟨2920570245943300687842341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947046830628867125228227 2920570245943300687842341)
                  ·
                    refine ⟨547606921114368878970439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920570245943300687842341 547606921114368878970439)
                    ·
                      rfl

theorem cell23_3199382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3199382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199382 prefixEnd_3199382 := by exact prefixLift 3199382
  have htrace : WordTrace (prefixWord ++ tailWord_3199382) baseStart_3199382 baseEnd_3199382 := by
    simpa [prefixWord, tailWord_3199382, baseEnd_3199382] using wordTrace_append hprefix tailTrace_3199382
  have hstable : (prefixWord ++ tailWord_3199382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199382).length < 2 ^ (prefixWord ++ tailWord_3199382).sum := by decide
  have hdescent : baseEnd_3199382 < baseStart_3199382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199397 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_3199397 : Nat := 118140960795 + 3199397 * 2 ^ 59
def prefixEnd_3199397 : Nat := 4983230072969 + 3 ^ 40 * 3199397 * 2
def baseEnd_3199397 : Nat := 1642828465552924078223747

theorem tailTrace_3199397 : CollatzResearch.WordTrace tailWord_3199397 prefixEnd_3199397 1642828465552924078223747 := by
  unfold tailWord_3199397
  simp only [CollatzResearch.WordTrace]
  refine ⟨116691595190138557350508445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77794396793425704900338963 116691595190138557350508445)
  ·
    refine ⟨43759348196301959006440667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116691595190138557350508445 43759348196301959006440667)
    ·
      refine ⟨65639022294452938509661001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43759348196301959006440667 65639022294452938509661001)
      ·
        refine ⟨49229266720839703882245751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65639022294452938509661001 49229266720839703882245751)
        ·
          refine ⟨73843900081259555823368627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49229266720839703882245751 73843900081259555823368627)
          ·
            refine ⟨110765850121889333735052941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73843900081259555823368627 110765850121889333735052941)
            ·
              refine ⟨41537193795708500150644853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110765850121889333735052941 41537193795708500150644853)
              ·
                refine ⟨3894111918347671889122955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41537193795708500150644853 3894111918347671889122955)
                ·
                  refine ⟨5841167877521507833684433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894111918347671889122955 5841167877521507833684433)
                  ·
                    refine ⟨4380875908141130875263325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5841167877521507833684433 4380875908141130875263325)
                    ·
                      refine ⟨1642828465552924078223747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380875908141130875263325 1642828465552924078223747)
                      ·
                        rfl

theorem cell23_3199397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_3199397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199397 prefixEnd_3199397 := by exact prefixLift 3199397
  have htrace : WordTrace (prefixWord ++ tailWord_3199397) baseStart_3199397 baseEnd_3199397 := by
    simpa [prefixWord, tailWord_3199397, baseEnd_3199397] using wordTrace_append hprefix tailTrace_3199397
  have hstable : (prefixWord ++ tailWord_3199397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199397).length < 2 ^ (prefixWord ++ tailWord_3199397).sum := by decide
  have hdescent : baseEnd_3199397 < baseStart_3199397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199405 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3199405 : Nat := 118140960795 + 3199405 * 2 ^ 59
def prefixEnd_3199405 : Nat := 4983230072969 + 3 ^ 40 * 3199405 * 2
def baseEnd_3199405 : Nat := 1642832573398160046923711

theorem tailTrace_3199405 : CollatzResearch.WordTrace tailWord_3199405 prefixEnd_3199405 1642832573398160046923711 := by
  unfold tailWord_3199405
  simp only [CollatzResearch.WordTrace]
  refine ⟨116691886974109574716799669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77794591316073049811199779 116691886974109574716799669)
  ·
    refine ⟨10939864403822772629699969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116691886974109574716799669 10939864403822772629699969)
    ·
      refine ⟨8204898302867079472274977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10939864403822772629699969 8204898302867079472274977)
      ·
        refine ⟨6153673727150309604206233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8204898302867079472274977 6153673727150309604206233)
        ·
          refine ⟨4615255295362732203154675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6153673727150309604206233 4615255295362732203154675)
          ·
            refine ⟨6922882943044098304732013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615255295362732203154675 6922882943044098304732013)
            ·
              refine ⟨2596081103641536864274505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6922882943044098304732013 2596081103641536864274505)
              ·
                refine ⟨1947060827731152648205879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596081103641536864274505 1947060827731152648205879)
                ·
                  refine ⟨2920591241596728972308819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947060827731152648205879 2920591241596728972308819)
                  ·
                    refine ⟨4380886862395093458463229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2920591241596728972308819 4380886862395093458463229)
                    ·
                      refine ⟨1642832573398160046923711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380886862395093458463229 1642832573398160046923711)
                      ·
                        rfl

theorem cell23_3199405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3199405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199405 prefixEnd_3199405 := by exact prefixLift 3199405
  have htrace : WordTrace (prefixWord ++ tailWord_3199405) baseStart_3199405 baseEnd_3199405 := by
    simpa [prefixWord, tailWord_3199405, baseEnd_3199405] using wordTrace_append hprefix tailTrace_3199405
  have hstable : (prefixWord ++ tailWord_3199405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199405).length < 2 ^ (prefixWord ++ tailWord_3199405).sum := by decide
  have hdescent : baseEnd_3199405 < baseStart_3199405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199421 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_3199421 : Nat := 118140960795 + 3199421 * 2 ^ 59
def prefixEnd_3199421 : Nat := 4983230072969 + 3 ^ 40 * 3199421 * 2
def baseEnd_3199421 : Nat := 547613596362877328107879

theorem tailTrace_3199421 : CollatzResearch.WordTrace tailWord_3199421 prefixEnd_3199421 547613596362877328107879 := by
  unfold tailWord_3199421
  simp only [CollatzResearch.WordTrace]
  refine ⟨116692470542051609449382117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77794980361367739632921411 116692470542051609449382117)
  ·
    refine ⟨21879838226634676771759147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116692470542051609449382117 21879838226634676771759147)
    ·
      refine ⟨32819757339952015157638721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21879838226634676771759147 32819757339952015157638721)
      ·
        refine ⟨24614818004964011368229041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32819757339952015157638721 24614818004964011368229041)
        ·
          refine ⟨18461113503723008526171781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24614818004964011368229041 18461113503723008526171781)
          ·
            refine ⟨3461458781948064098657209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18461113503723008526171781 3461458781948064098657209)
            ·
              refine ⟨2596094086461048073992907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461458781948064098657209 2596094086461048073992907)
              ·
                refine ⟨3894141129691572110989361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596094086461048073992907 3894141129691572110989361)
                ·
                  refine ⟨2920605847268679083242021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3894141129691572110989361 2920605847268679083242021)
                  ·
                    refine ⟨547613596362877328107879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920605847268679083242021 547613596362877328107879)
                    ·
                      rfl

theorem cell23_3199421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_3199421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199421 prefixEnd_3199421 := by exact prefixLift 3199421
  have htrace : WordTrace (prefixWord ++ tailWord_3199421) baseStart_3199421 baseEnd_3199421 := by
    simpa [prefixWord, tailWord_3199421, baseEnd_3199421] using wordTrace_append hprefix tailTrace_3199421
  have hstable : (prefixWord ++ tailWord_3199421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199421).length < 2 ^ (prefixWord ++ tailWord_3199421).sum := by decide
  have hdescent : baseEnd_3199421 < baseStart_3199421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199425 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3199425 : Nat := 118140960795 + 3199425 * 2 ^ 59
def prefixEnd_3199425 : Nat := 4983230072969 + 3 ^ 40 * 3199425 * 2
def baseEnd_3199425 : Nat := 547614281003749989557873

theorem tailTrace_3199425 : CollatzResearch.WordTrace tailWord_3199425 prefixEnd_3199425 547614281003749989557873 := by
  unfold tailWord_3199425
  simp only [CollatzResearch.WordTrace]
  refine ⟨116692616434037118132527729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77795077622691412088351819 116692616434037118132527729)
  ·
    refine ⟨87519462325527838599395797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116692616434037118132527729 87519462325527838599395797)
    ·
      refine ⟨2051237398254558717173339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 87519462325527838599395797 2051237398254558717173339)
      ·
        refine ⟨3076856097381838075760009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051237398254558717173339 3076856097381838075760009)
        ·
          refine ⟨2307642073036378556820007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3076856097381838075760009 2307642073036378556820007)
          ·
            refine ⟨3461463109554567835230011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307642073036378556820007 3461463109554567835230011)
            ·
              refine ⟨5192194664331851752845017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461463109554567835230011 5192194664331851752845017)
              ·
                refine ⟨3894145998248888814633763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192194664331851752845017 3894145998248888814633763)
                ·
                  refine ⟨5841218997373333221950645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894145998248888814633763 5841218997373333221950645)
                  ·
                    refine ⟨547614281003749989557873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5841218997373333221950645 547614281003749989557873)
                    ·
                      rfl

theorem cell23_3199425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3199425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199425 prefixEnd_3199425 := by exact prefixLift 3199425
  have htrace : WordTrace (prefixWord ++ tailWord_3199425) baseStart_3199425 baseEnd_3199425 := by
    simpa [prefixWord, tailWord_3199425, baseEnd_3199425] using wordTrace_append hprefix tailTrace_3199425
  have hstable : (prefixWord ++ tailWord_3199425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199425).length < 2 ^ (prefixWord ++ tailWord_3199425).sum := by decide
  have hdescent : baseEnd_3199425 < baseStart_3199425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199428 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3199428 : Nat := 118140960795 + 3199428 * 2 ^ 59
def prefixEnd_3199428 : Nat := 4983230072969 + 3 ^ 40 * 3199428 * 2
def baseEnd_3199428 : Nat := 1642844383453213456936105

theorem tailTrace_3199428 : CollatzResearch.WordTrace tailWord_3199428 prefixEnd_3199428 1642844383453213456936105 := by
  unfold tailWord_3199428
  simp only [CollatzResearch.WordTrace]
  refine ⟨58346362926513124822443469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77795150568684166429924625 58346362926513124822443469)
  ·
    refine ⟨21879886097442421808416301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58346362926513124822443469 21879886097442421808416301)
    ·
      refine ⟨8204957286540908178156113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21879886097442421808416301 8204957286540908178156113)
      ·
        refine ⟨6153717964905681133617085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8204957286540908178156113 6153717964905681133617085)
        ·
          refine ⟨2307644236839630425106407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6153717964905681133617085 2307644236839630425106407)
          ·
            refine ⟨3461466355259445637659611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307644236839630425106407 3461466355259445637659611)
            ·
              refine ⟨5192199532889168456489417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461466355259445637659611 5192199532889168456489417)
              ·
                refine ⟨3894149649666876342367063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192199532889168456489417 3894149649666876342367063)
                ·
                  refine ⟨5841224474500314513550595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894149649666876342367063 5841224474500314513550595)
                  ·
                    refine ⟨8761836711750471770325893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5841224474500314513550595 8761836711750471770325893)
                    ·
                      refine ⟨1642844383453213456936105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8761836711750471770325893 1642844383453213456936105)
                      ·
                        rfl

theorem cell23_3199428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3199428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199428 prefixEnd_3199428 := by exact prefixLift 3199428
  have htrace : WordTrace (prefixWord ++ tailWord_3199428) baseStart_3199428 baseEnd_3199428 := by
    simpa [prefixWord, tailWord_3199428, baseEnd_3199428] using wordTrace_append hprefix tailTrace_3199428
  have hstable : (prefixWord ++ tailWord_3199428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199428).length < 2 ^ (prefixWord ++ tailWord_3199428).sum := by decide
  have hdescent : baseEnd_3199428 < baseStart_3199428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199444 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3199444 : Nat := 118140960795 + 3199444 * 2 ^ 59
def prefixEnd_3199444 : Nat := 4983230072969 + 3 ^ 40 * 3199444 * 2
def baseEnd_3199444 : Nat := 1642852599143685394336031

theorem tailTrace_3199444 : CollatzResearch.WordTrace tailWord_3199444 prefixEnd_3199444 1642852599143685394336031 := by
  unfold tailWord_3199444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58346654710484142188734693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77795539613978856251646257 58346654710484142188734693)
  ·
    refine ⟨10939997758215776660387755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58346654710484142188734693 10939997758215776660387755)
    ·
      refine ⟨16409996637323664990581633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10939997758215776660387755 16409996637323664990581633)
      ·
        refine ⟨12307497477992748742936225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16409996637323664990581633 12307497477992748742936225)
        ·
          refine ⟨9230623108494561557202169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12307497477992748742936225 9230623108494561557202169)
          ·
            refine ⟨6922967331370921167901627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9230623108494561557202169 6922967331370921167901627)
            ·
              refine ⟨10384450997056381751852441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6922967331370921167901627 10384450997056381751852441)
              ·
                refine ⟨7788338247792286313889331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10384450997056381751852441 7788338247792286313889331)
                ·
                  refine ⟨11682507371688429470833997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788338247792286313889331 11682507371688429470833997)
                  ·
                    refine ⟨4380940264383161051562749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11682507371688429470833997 4380940264383161051562749)
                    ·
                      refine ⟨1642852599143685394336031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4380940264383161051562749 1642852599143685394336031)
                      ·
                        rfl

theorem cell23_3199444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3199444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199444 prefixEnd_3199444 := by exact prefixLift 3199444
  have htrace : WordTrace (prefixWord ++ tailWord_3199444) baseStart_3199444 baseEnd_3199444 := by
    simpa [prefixWord, tailWord_3199444, baseEnd_3199444] using wordTrace_append hprefix tailTrace_3199444
  have hstable : (prefixWord ++ tailWord_3199444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199444).length < 2 ^ (prefixWord ++ tailWord_3199444).sum := by decide
  have hdescent : baseEnd_3199444 < baseStart_3199444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199467 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 3, 4, 2]
def baseStart_3199467 : Nat := 118140960795 + 3199467 * 2 ^ 59
def prefixEnd_3199467 : Nat := 4983230072969 + 3 ^ 40 * 3199467 * 2
def baseEnd_3199467 : Nat := 1642864409198738804348425

theorem tailTrace_3199467 : CollatzResearch.WordTrace tailWord_3199467 prefixEnd_3199467 1642864409198738804348425 := by
  unfold tailWord_3199467
  simp only [CollatzResearch.WordTrace]
  refine ⟨116694148299884959305556655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77796098866589972870371103 116694148299884959305556655)
  ·
    refine ⟨175041222449827438958334983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116694148299884959305556655 175041222449827438958334983)
    ·
      refine ⟨262561833674741158437502475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175041222449827438958334983 262561833674741158437502475)
      ·
        refine ⟨393842750512111737656253713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262561833674741158437502475 393842750512111737656253713)
        ·
          refine ⟨295382062884083803242190285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393842750512111737656253713 295382062884083803242190285)
          ·
            refine ⟨110768273581531426215821357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295382062884083803242190285 110768273581531426215821357)
            ·
              refine ⟨41538102593074284830933009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110768273581531426215821357 41538102593074284830933009)
              ·
                refine ⟨31153576944805713623199757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41538102593074284830933009 31153576944805713623199757)
                ·
                  refine ⟨11682591354302142608699909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31153576944805713623199757 11682591354302142608699909)
                  ·
                    refine ⟨2190485878931651739131233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11682591354302142608699909 2190485878931651739131233)
                    ·
                      refine ⟨1642864409198738804348425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2190485878931651739131233 1642864409198738804348425)
                      ·
                        rfl

theorem cell23_3199467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4, 2].length) (baseStart_3199467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199467 prefixEnd_3199467 := by exact prefixLift 3199467
  have htrace : WordTrace (prefixWord ++ tailWord_3199467) baseStart_3199467 baseEnd_3199467 := by
    simpa [prefixWord, tailWord_3199467, baseEnd_3199467] using wordTrace_append hprefix tailTrace_3199467
  have hstable : (prefixWord ++ tailWord_3199467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199467).length < 2 ^ (prefixWord ++ tailWord_3199467).sum := by decide
  have hdescent : baseEnd_3199467 < baseStart_3199467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199484 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_3199484 : Nat := 118140960795 + 3199484 * 2 ^ 59
def prefixEnd_3199484 : Nat := 4983230072969 + 3 ^ 40 * 3199484 * 2
def baseEnd_3199484 : Nat := 1642873138369865237835847

theorem tailTrace_3199484 : CollatzResearch.WordTrace tailWord_3199484 prefixEnd_3199484 1642873138369865237835847 := by
  unfold tailWord_3199484
  simp only [CollatzResearch.WordTrace]
  refine ⟨58347384170411685604462753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77796512227215580805950337 58347384170411685604462753)
  ·
    refine ⟨43760538127808764203347065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58347384170411685604462753 43760538127808764203347065)
    ·
      refine ⟨32820403595856573152510299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43760538127808764203347065 32820403595856573152510299)
      ·
        refine ⟨49230605393784859728765449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32820403595856573152510299 49230605393784859728765449)
        ·
          refine ⟨36922954045338644796574087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49230605393784859728765449 36922954045338644796574087)
          ·
            refine ⟨55384431068007967194861131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36922954045338644796574087 55384431068007967194861131)
            ·
              refine ⟨83076646602011950792291697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55384431068007967194861131 83076646602011950792291697)
              ·
                refine ⟨62307484951508963094218773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83076646602011950792291697 62307484951508963094218773)
                ·
                  refine ⟨2920663357101982645041505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62307484951508963094218773 2920663357101982645041505)
                  ·
                    refine ⟨2190497517826486983781129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2920663357101982645041505 2190497517826486983781129)
                    ·
                      refine ⟨1642873138369865237835847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2190497517826486983781129 1642873138369865237835847)
                      ·
                        rfl

theorem cell23_3199484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_3199484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199484 prefixEnd_3199484 := by exact prefixLift 3199484
  have htrace : WordTrace (prefixWord ++ tailWord_3199484) baseStart_3199484 baseEnd_3199484 := by
    simpa [prefixWord, tailWord_3199484, baseEnd_3199484] using wordTrace_append hprefix tailTrace_3199484
  have hstable : (prefixWord ++ tailWord_3199484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199484).length < 2 ^ (prefixWord ++ tailWord_3199484).sum := by decide
  have hdescent : baseEnd_3199484 < baseStart_3199484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199557 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_3199557 : Nat := 118140960795 + 3199557 * 2 ^ 59
def prefixEnd_3199557 : Nat := 4983230072969 + 3 ^ 40 * 3199557 * 2
def baseEnd_3199557 : Nat := 1642910622457643452223011

theorem tailTrace_3199557 : CollatzResearch.WordTrace tailWord_3199557 prefixEnd_3199557 1642910622457643452223011 := by
  unfold tailWord_3199557
  simp only [CollatzResearch.WordTrace]
  refine ⟨116697430869558904676332925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77798287246372603117555283 116697430869558904676332925)
  ·
    refine ⟨43761536576084589253624847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116697430869558904676332925 43761536576084589253624847)
    ·
      refine ⟨65642304864126883880437271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43761536576084589253624847 65642304864126883880437271)
      ·
        refine ⟨98463457296190325820655907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65642304864126883880437271 98463457296190325820655907)
        ·
          refine ⟨147695185944285488730983861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98463457296190325820655907 147695185944285488730983861)
          ·
            refine ⟨13846423682276764568529737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147695185944285488730983861 13846423682276764568529737)
            ·
              refine ⟨10384817761707573426397303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13846423682276764568529737 10384817761707573426397303)
              ·
                refine ⟨15577226642561360139595955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10384817761707573426397303 15577226642561360139595955)
                ·
                  refine ⟨23365839963842040209393933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15577226642561360139595955 23365839963842040209393933)
                  ·
                    refine ⟨8762189986440765078522725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23365839963842040209393933 8762189986440765078522725)
                    ·
                      refine ⟨1642910622457643452223011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8762189986440765078522725 1642910622457643452223011)
                      ·
                        rfl

theorem cell23_3199557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_3199557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199557 prefixEnd_3199557 := by exact prefixLift 3199557
  have htrace : WordTrace (prefixWord ++ tailWord_3199557) baseStart_3199557 baseEnd_3199557 := by
    simpa [prefixWord, tailWord_3199557, baseEnd_3199557] using wordTrace_append hprefix tailTrace_3199557
  have hstable : (prefixWord ++ tailWord_3199557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199557).length < 2 ^ (prefixWord ++ tailWord_3199557).sum := by decide
  have hdescent : baseEnd_3199557 < baseStart_3199557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199558 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_3199558 : Nat := 118140960795 + 3199558 * 2 ^ 59
def prefixEnd_3199558 : Nat := 4983230072969 + 3 ^ 40 * 3199558 * 2
def baseEnd_3199558 : Nat := 182545681770921994256723

theorem tailTrace_3199558 : CollatzResearch.WordTrace tailWord_3199558 prefixEnd_3199558 182545681770921994256723 := by
  unfold tailWord_3199558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646795854454852557722479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77798311561703521231412885 3646795854454852557722479)
  ·
    refine ⟨5470193781682278836583719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3646795854454852557722479 5470193781682278836583719)
    ·
      refine ⟨8205290672523418254875579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470193781682278836583719 8205290672523418254875579)
      ·
        refine ⟨12307936008785127382313369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205290672523418254875579 12307936008785127382313369)
        ·
          refine ⟨9230952006588845536735027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12307936008785127382313369 9230952006588845536735027)
          ·
            refine ⟨13846428009883268305102541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9230952006588845536735027 13846428009883268305102541)
            ·
              refine ⟨5192410503706225614413453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13846428009883268305102541 5192410503706225614413453)
              ·
                refine ⟨1947153938889834605405045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5192410503706225614413453 1947153938889834605405045)
                ·
                  refine ⟨182545681770921994256723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947153938889834605405045 182545681770921994256723)
                  ·
                    rfl

theorem cell23_3199558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_3199558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199558 prefixEnd_3199558 := by exact prefixLift 3199558
  have htrace : WordTrace (prefixWord ++ tailWord_3199558) baseStart_3199558 baseEnd_3199558 := by
    simpa [prefixWord, tailWord_3199558, baseEnd_3199558] using wordTrace_append hprefix tailTrace_3199558
  have hstable : (prefixWord ++ tailWord_3199558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199558).length < 2 ^ (prefixWord ++ tailWord_3199558).sum := by decide
  have hdescent : baseEnd_3199558 < baseStart_3199558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199567 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 5, 4]
def baseStart_3199567 : Nat := 118140960795 + 3199567 * 2 ^ 59
def prefixEnd_3199567 : Nat := 4983230072969 + 3 ^ 40 * 3199567 * 2
def baseEnd_3199567 : Nat := 547638585754729471032655

theorem tailTrace_3199567 : CollatzResearch.WordTrace tailWord_3199567 prefixEnd_3199567 547638585754729471032655 := by
  unfold tailWord_3199567
  simp only [CollatzResearch.WordTrace]
  refine ⟨116697795599522676384196955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77798530399681784256131303 116697795599522676384196955)
  ·
    refine ⟨175046693399284014576295433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116697795599522676384196955 175046693399284014576295433)
    ·
      refine ⟨131285020049463010932221575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175046693399284014576295433 131285020049463010932221575)
      ·
        refine ⟨196927530074194516398332363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131285020049463010932221575 196927530074194516398332363)
        ·
          refine ⟨295391295111291774597498545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196927530074194516398332363 295391295111291774597498545)
          ·
            refine ⟨221543471333468830948123909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295391295111291774597498545 221543471333468830948123909)
            ·
              refine ⟨41539400875025405802773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221543471333468830948123909 41539400875025405802773233)
              ·
                refine ⟨31154550656269054352079925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41539400875025405802773233 31154550656269054352079925)
                ·
                  refine ⟨2920739124025223845507493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31154550656269054352079925 2920739124025223845507493)
                  ·
                    refine ⟨547638585754729471032655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920739124025223845507493 547638585754729471032655)
                    ·
                      rfl

theorem cell23_3199567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_3199567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199567 prefixEnd_3199567 := by exact prefixLift 3199567
  have htrace : WordTrace (prefixWord ++ tailWord_3199567) baseStart_3199567 baseEnd_3199567 := by
    simpa [prefixWord, tailWord_3199567, baseEnd_3199567] using wordTrace_append hprefix tailTrace_3199567
  have hstable : (prefixWord ++ tailWord_3199567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199567).length < 2 ^ (prefixWord ++ tailWord_3199567).sum := by decide
  have hdescent : baseEnd_3199567 < baseStart_3199567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199584 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_3199584 : Nat := 118140960795 + 3199584 * 2 ^ 59
def prefixEnd_3199584 : Nat := 4983230072969 + 3 ^ 40 * 3199584 * 2
def baseEnd_3199584 : Nat := 547641495478438282195129

theorem tailTrace_3199584 : CollatzResearch.WordTrace tailWord_3199584 prefixEnd_3199584 547641495478438282195129 := by
  unfold tailWord_3199584
  simp only [CollatzResearch.WordTrace]
  refine ⟨58349207820230544143782903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77798943760307392191710537 58349207820230544143782903)
  ·
    refine ⟨87523811730345816215674355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58349207820230544143782903 87523811730345816215674355)
    ·
      refine ⟨131285717595518724323511533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87523811730345816215674355 131285717595518724323511533)
      ·
        refine ⟨49232144098319521621316825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131285717595518724323511533 49232144098319521621316825)
        ·
          refine ⟨36924108073739641215987619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49232144098319521621316825 36924108073739641215987619)
          ·
            refine ⟨55386162110609461823981429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36924108073739641215987619 55386162110609461823981429)
            ·
              refine ⟨5192452697869637045998259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55386162110609461823981429 5192452697869637045998259)
              ·
                refine ⟨7788679046804455568997389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192452697869637045998259 7788679046804455568997389)
                ·
                  refine ⟨2920754642551670838374021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7788679046804455568997389 2920754642551670838374021)
                  ·
                    refine ⟨547641495478438282195129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920754642551670838374021 547641495478438282195129)
                    ·
                      rfl

theorem cell23_3199584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_3199584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199584 prefixEnd_3199584 := by exact prefixLift 3199584
  have htrace : WordTrace (prefixWord ++ tailWord_3199584) baseStart_3199584 baseEnd_3199584 := by
    simpa [prefixWord, tailWord_3199584, baseEnd_3199584] using wordTrace_append hprefix tailTrace_3199584
  have hstable : (prefixWord ++ tailWord_3199584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199584).length < 2 ^ (prefixWord ++ tailWord_3199584).sum := by decide
  have hdescent : baseEnd_3199584 < baseStart_3199584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199594 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3199594 : Nat := 118140960795 + 3199594 * 2 ^ 59
def prefixEnd_3199594 : Nat := 4983230072969 + 3 ^ 40 * 3199594 * 2
def baseEnd_3199594 : Nat := 1642929621241859807460341

theorem tailTrace_3199594 : CollatzResearch.WordTrace tailWord_3199594 prefixEnd_3199594 1642929621241859807460341 := by
  unfold tailWord_3199594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29174695092606214998857459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77799186913616573330286557 29174695092606214998857459)
  ·
    refine ⟨43762042638909322498286189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29174695092606214998857459 43762042638909322498286189)
    ·
      refine ⟨16410765989590995936857321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43762042638909322498286189 16410765989590995936857321)
      ·
        refine ⟨12308074492193246952642991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16410765989590995936857321 12308074492193246952642991)
        ·
          refine ⟨18462111738289870428964487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12308074492193246952642991 18462111738289870428964487)
          ·
            refine ⟨27693167607434805643446731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18462111738289870428964487 27693167607434805643446731)
            ·
              refine ⟨41539751411152208465170097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27693167607434805643446731 41539751411152208465170097)
              ·
                refine ⟨31154813558364156348877573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41539751411152208465170097 31154813558364156348877573)
                ·
                  refine ⟨5841527542193279315414545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31154813558364156348877573 5841527542193279315414545)
                  ·
                    refine ⟨4381145656644959486560909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5841527542193279315414545 4381145656644959486560909)
                    ·
                      refine ⟨1642929621241859807460341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381145656644959486560909 1642929621241859807460341)
                      ·
                        rfl

theorem cell23_3199594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3199594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199594 prefixEnd_3199594 := by exact prefixLift 3199594
  have htrace : WordTrace (prefixWord ++ tailWord_3199594) baseStart_3199594 baseEnd_3199594 := by
    simpa [prefixWord, tailWord_3199594, baseEnd_3199594] using wordTrace_append hprefix tailTrace_3199594
  have hstable : (prefixWord ++ tailWord_3199594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199594).length < 2 ^ (prefixWord ++ tailWord_3199594).sum := by decide
  have hdescent : baseEnd_3199594 < baseStart_3199594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199607 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_3199607 : Nat := 118140960795 + 3199607 * 2 ^ 59
def prefixEnd_3199607 : Nat := 4983230072969 + 3 ^ 40 * 3199607 * 2
def baseEnd_3199607 : Nat := 1642936296490368256597781

theorem tailTrace_3199607 : CollatzResearch.WordTrace tailWord_3199607 prefixEnd_3199607 1642936296490368256597781 := by
  unfold tailWord_3199607
  simp only [CollatzResearch.WordTrace]
  refine ⟨116699254519377763215653075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77799503012918508810435383 116699254519377763215653075)
  ·
    refine ⟨175048881779066644823479613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116699254519377763215653075 175048881779066644823479613)
    ·
      refine ⟨65643330667149991808804855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175048881779066644823479613 65643330667149991808804855)
      ·
        refine ⟨98464996000724987713207283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65643330667149991808804855 98464996000724987713207283)
        ·
          refine ⟨147697494001087481569810925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98464996000724987713207283 147697494001087481569810925)
          ·
            refine ⟨55386560250407805588679097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147697494001087481569810925 55386560250407805588679097)
            ·
              refine ⟨41539920187805854191509323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55386560250407805588679097 41539920187805854191509323)
              ·
                refine ⟨62309880281708781287263985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41539920187805854191509323 62309880281708781287263985)
                ·
                  refine ⟨46732410211281585965447989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62309880281708781287263985 46732410211281585965447989)
                  ·
                    refine ⟨4381163457307648684260749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46732410211281585965447989 4381163457307648684260749)
                    ·
                      refine ⟨1642936296490368256597781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381163457307648684260749 1642936296490368256597781)
                      ·
                        rfl

theorem cell23_3199607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_3199607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199607 prefixEnd_3199607 := by exact prefixLift 3199607
  have htrace : WordTrace (prefixWord ++ tailWord_3199607) baseStart_3199607 baseEnd_3199607 := by
    simpa [prefixWord, tailWord_3199607, baseEnd_3199607] using wordTrace_append hprefix tailTrace_3199607
  have hstable : (prefixWord ++ tailWord_3199607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199607).length < 2 ^ (prefixWord ++ tailWord_3199607).sum := by decide
  have hdescent : baseEnd_3199607 < baseStart_3199607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199644 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_3199644 : Nat := 118140960795 + 3199644 * 2 ^ 59
def prefixEnd_3199644 : Nat := 4983230072969 + 3 ^ 40 * 3199644 * 2
def baseEnd_3199644 : Nat := 547651765091528203945037

theorem tailTrace_3199644 : CollatzResearch.WordTrace tailWord_3199644 prefixEnd_3199644 547651765091528203945037 := by
  unfold tailWord_3199644
  simp only [CollatzResearch.WordTrace]
  refine ⟨58350302010121859267374993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77800402680162479023166657 58350302010121859267374993)
  ·
    refine ⟨43762726507591394450531245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58350302010121859267374993 43762726507591394450531245)
    ·
      refine ⟨16411022440346772918949217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43762726507591394450531245 16411022440346772918949217)
      ·
        refine ⟨12308266830260079689211913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16411022440346772918949217 12308266830260079689211913)
        ·
          refine ⟨9231200122695059766908935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12308266830260079689211913 9231200122695059766908935)
          ·
            refine ⟨13846800184042589650363403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9231200122695059766908935 13846800184042589650363403)
            ·
              refine ⟨20770200276063884475545105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846800184042589650363403 20770200276063884475545105)
              ·
                refine ⟨15577650207047913356658829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20770200276063884475545105 15577650207047913356658829)
                ·
                  refine ⟨5841618827642967508747061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15577650207047913356658829 5841618827642967508747061)
                  ·
                    refine ⟨547651765091528203945037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5841618827642967508747061 547651765091528203945037)
                    ·
                      rfl

theorem cell23_3199644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_3199644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199644 prefixEnd_3199644 := by exact prefixLift 3199644
  have htrace : WordTrace (prefixWord ++ tailWord_3199644) baseStart_3199644 baseEnd_3199644 := by
    simpa [prefixWord, tailWord_3199644, baseEnd_3199644] using wordTrace_append hprefix tailTrace_3199644
  have hstable : (prefixWord ++ tailWord_3199644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199644).length < 2 ^ (prefixWord ++ tailWord_3199644).sum := by decide
  have hdescent : baseEnd_3199644 < baseStart_3199644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199657 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_3199657 : Nat := 118140960795 + 3199657 * 2 ^ 59
def prefixEnd_3199657 : Nat := 4983230072969 + 3 ^ 40 * 3199657 * 2
def baseEnd_3199657 : Nat := 547653990174364353657517

theorem tailTrace_3199657 : CollatzResearch.WordTrace tailWord_3199657 prefixEnd_3199657 547653990174364353657517 := by
  unfold tailWord_3199657
  simp only [CollatzResearch.WordTrace]
  refine ⟨116701078169196621754973225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77800718779464414503315483 116701078169196621754973225)
  ·
    refine ⟨87525808626897466316229919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116701078169196621754973225 87525808626897466316229919)
    ·
      refine ⟨131288712940346199474344879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87525808626897466316229919 131288712940346199474344879)
      ·
        refine ⟨196933069410519299211517319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131288712940346199474344879 196933069410519299211517319)
        ·
          refine ⟨295399604115778948817275979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196933069410519299211517319 295399604115778948817275979)
          ·
            refine ⟨443099406173668423225913969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295399604115778948817275979 443099406173668423225913969)
            ·
              refine ⟨332324554630251317419435477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443099406173668423225913969 332324554630251317419435477)
              ·
                refine ⟨7788856749146515252018019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 332324554630251317419435477 7788856749146515252018019)
                ·
                  refine ⟨11683285123719772878027029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788856749146515252018019 11683285123719772878027029)
                  ·
                    refine ⟨547653990174364353657517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11683285123719772878027029 547653990174364353657517)
                    ·
                      rfl

theorem cell23_3199657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_3199657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199657 prefixEnd_3199657 := by exact prefixLift 3199657
  have htrace : WordTrace (prefixWord ++ tailWord_3199657) baseStart_3199657 baseEnd_3199657 := by
    simpa [prefixWord, tailWord_3199657, baseEnd_3199657] using wordTrace_append hprefix tailTrace_3199657
  have hstable : (prefixWord ++ tailWord_3199657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199657).length < 2 ^ (prefixWord ++ tailWord_3199657).sum := by decide
  have hdescent : baseEnd_3199657 < baseStart_3199657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199664 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_3199664 : Nat := 118140960795 + 3199664 * 2 ^ 59
def prefixEnd_3199664 : Nat := 4983230072969 + 3 ^ 40 * 3199664 * 2
def baseEnd_3199664 : Nat := 1642965564887674533585019

theorem tailTrace_3199664 : CollatzResearch.WordTrace tailWord_3199664 prefixEnd_3199664 1642965564887674533585019 := by
  unfold tailWord_3199664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58350666740085630975239023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77800888986780841300318697 58350666740085630975239023)
  ·
    refine ⟨87526000110128446462858535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58350666740085630975239023 87526000110128446462858535)
    ·
      refine ⟨131289000165192669694287803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87526000110128446462858535 131289000165192669694287803)
      ·
        refine ⟨196933500247789004541431705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131289000165192669694287803 196933500247789004541431705)
        ·
          refine ⟨147700125185841753406073779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196933500247789004541431705 147700125185841753406073779)
          ·
            refine ⟨221550187778762630109110669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147700125185841753406073779 221550187778762630109110669)
            ·
              refine ⟨83081320417035986290916501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221550187778762630109110669 83081320417035986290916501)
              ·
                refine ⟨3894436894548561857386711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83081320417035986290916501 3894436894548561857386711)
                ·
                  refine ⟨5841655341822842786080067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894436894548561857386711 5841655341822842786080067)
                  ·
                    refine ⟨8762483012734264179120101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5841655341822842786080067 8762483012734264179120101)
                    ·
                      refine ⟨1642965564887674533585019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8762483012734264179120101 1642965564887674533585019)
                      ·
                        rfl

theorem cell23_3199664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_3199664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199664 prefixEnd_3199664 := by exact prefixLift 3199664
  have htrace : WordTrace (prefixWord ++ tailWord_3199664) baseStart_3199664 baseEnd_3199664 := by
    simpa [prefixWord, tailWord_3199664, baseEnd_3199664] using wordTrace_append hprefix tailTrace_3199664
  have hstable : (prefixWord ++ tailWord_3199664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199664).length < 2 ^ (prefixWord ++ tailWord_3199664).sum := by decide
  have hdescent : baseEnd_3199664 < baseStart_3199664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199674 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_3199674 : Nat := 118140960795 + 3199674 * 2 ^ 59
def prefixEnd_3199674 : Nat := 4983230072969 + 3 ^ 40 * 3199674 * 2
def baseEnd_3199674 : Nat := 547656899898073164819991

theorem tailTrace_3199674 : CollatzResearch.WordTrace tailWord_3199674 prefixEnd_3199674 547656899898073164819991 := by
  unfold tailWord_3199674
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175424552533758414585519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77801132140090022438894717 29175424552533758414585519)
  ·
    refine ⟨43763136828800637621878279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29175424552533758414585519 43763136828800637621878279)
    ·
      refine ⟨65644705243200956432817419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43763136828800637621878279 65644705243200956432817419)
      ·
        refine ⟨98467057864801434649226129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65644705243200956432817419 98467057864801434649226129)
        ·
          refine ⟨73850293398601075986919597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98467057864801434649226129 73850293398601075986919597)
          ·
            refine ⟨27693860024475403495094849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73850293398601075986919597 27693860024475403495094849)
            ·
              refine ⟨20770395018356552621321137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27693860024475403495094849 20770395018356552621321137)
              ·
                refine ⟨15577796263767414465990853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20770395018356552621321137 15577796263767414465990853)
                ·
                  refine ⟨2920836799456390212373285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15577796263767414465990853 2920836799456390212373285)
                  ·
                    refine ⟨547656899898073164819991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920836799456390212373285 547656899898073164819991)
                    ·
                      rfl

theorem cell23_3199674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_3199674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199674 prefixEnd_3199674 := by exact prefixLift 3199674
  have htrace : WordTrace (prefixWord ++ tailWord_3199674) baseStart_3199674 baseEnd_3199674 := by
    simpa [prefixWord, tailWord_3199674, baseEnd_3199674] using wordTrace_append hprefix tailTrace_3199674
  have hstable : (prefixWord ++ tailWord_3199674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199674).length < 2 ^ (prefixWord ++ tailWord_3199674).sum := by decide
  have hdescent : baseEnd_3199674 < baseStart_3199674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199708 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3199708 : Nat := 118140960795 + 3199708 * 2 ^ 59
def prefixEnd_3199708 : Nat := 4983230072969 + 3 ^ 40 * 3199708 * 2
def baseEnd_3199708 : Nat := 547662719345490787144939

theorem tailTrace_3199708 : CollatzResearch.WordTrace tailWord_3199708 prefixEnd_3199708 547662719345490787144939 := by
  unfold tailWord_3199708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58351469146005928732539889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77801958861341238310053185 58351469146005928732539889)
  ·
    refine ⟨43763601859504446549404917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58351469146005928732539889 43763601859504446549404917)
    ·
      refine ⟨4102837674328541864006711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43763601859504446549404917 4102837674328541864006711)
      ·
        refine ⟨6154256511492812796010067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102837674328541864006711 6154256511492812796010067)
        ·
          refine ⟨9231384767239219194015101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154256511492812796010067 9231384767239219194015101)
          ·
            refine ⟨3461769287714707197755663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9231384767239219194015101 3461769287714707197755663)
            ·
              refine ⟨5192653931572060796633495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461769287714707197755663 5192653931572060796633495)
              ·
                refine ⟨7788980897358091194950243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192653931572060796633495 7788980897358091194950243)
                ·
                  refine ⟨11683471346037136792425365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788980897358091194950243 11683471346037136792425365)
                  ·
                    refine ⟨547662719345490787144939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11683471346037136792425365 547662719345490787144939)
                    ·
                      rfl

theorem cell23_3199708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3199708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199708 prefixEnd_3199708 := by exact prefixLift 3199708
  have htrace : WordTrace (prefixWord ++ tailWord_3199708) baseStart_3199708 baseEnd_3199708 := by
    simpa [prefixWord, tailWord_3199708, baseEnd_3199708] using wordTrace_append hprefix tailTrace_3199708
  have hstable : (prefixWord ++ tailWord_3199708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199708).length < 2 ^ (prefixWord ++ tailWord_3199708).sum := by decide
  have hdescent : baseEnd_3199708 < baseStart_3199708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199711 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_3199711 : Nat := 118140960795 + 3199711 * 2 ^ 59
def prefixEnd_3199711 : Nat := 4983230072969 + 3 ^ 40 * 3199711 * 2
def baseEnd_3199711 : Nat := 1642989698478435849697303

theorem tailTrace_3199711 : CollatzResearch.WordTrace tailWord_3199711 prefixEnd_3199711 1642989698478435849697303 := by
  unfold tailWord_3199711
  simp only [CollatzResearch.WordTrace]
  refine ⟨116703047711000988977438987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77802031807333992651625991 116703047711000988977438987)
  ·
    refine ⟨175054571566501483466158481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116703047711000988977438987 175054571566501483466158481)
    ·
      refine ⟨131290928674876112599618861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175054571566501483466158481 131290928674876112599618861)
      ·
        refine ⟨49234098253078542224857073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131290928674876112599618861 49234098253078542224857073)
        ·
          refine ⟨36925573689808906668642805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49234098253078542224857073 36925573689808906668642805)
          ·
            refine ⟨3461772533419585000185263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36925573689808906668642805 3461772533419585000185263)
            ·
              refine ⟨5192658800129377500277895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461772533419585000185263 5192658800129377500277895)
              ·
                refine ⟨7788988200194066250416843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192658800129377500277895 7788988200194066250416843)
                ·
                  refine ⟨11683482300291099375625265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788988200194066250416843 11683482300291099375625265)
                  ·
                    refine ⟨8762611725218324531718949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11683482300291099375625265 8762611725218324531718949)
                    ·
                      refine ⟨1642989698478435849697303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8762611725218324531718949 1642989698478435849697303)
                      ·
                        rfl

theorem cell23_3199711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_3199711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199711 prefixEnd_3199711 := by exact prefixLift 3199711
  have htrace : WordTrace (prefixWord ++ tailWord_3199711) baseStart_3199711 baseEnd_3199711 := by
    simpa [prefixWord, tailWord_3199711, baseEnd_3199711] using wordTrace_append hprefix tailTrace_3199711
  have hstable : (prefixWord ++ tailWord_3199711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199711).length < 2 ^ (prefixWord ++ tailWord_3199711).sum := by decide
  have hdescent : baseEnd_3199711 < baseStart_3199711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199737 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3199737 : Nat := 118140960795 + 3199737 * 2 ^ 59
def prefixEnd_3199737 : Nat := 4983230072969 + 3 ^ 40 * 3199737 * 2
def baseEnd_3199737 : Nat := 1643003048975452747972183

theorem tailTrace_3199737 : CollatzResearch.WordTrace tailWord_3199737 prefixEnd_3199737 1643003048975452747972183 := by
  unfold tailWord_3199737
  simp only [CollatzResearch.WordTrace]
  refine ⟨116703996008906795417885465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77802664005937863611923643 116703996008906795417885465)
  ·
    refine ⟨87527997006680096563414099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116703996008906795417885465 87527997006680096563414099)
    ·
      refine ⟨131291995510020144845121149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87527997006680096563414099 131291995510020144845121149)
      ·
        refine ⟨49234498316257554316920431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131291995510020144845121149 49234498316257554316920431)
        ·
          refine ⟨73851747474386331475380647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49234498316257554316920431 73851747474386331475380647)
          ·
            refine ⟨110777621211579497213070971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73851747474386331475380647 110777621211579497213070971)
            ·
              refine ⟨166166431817369245819606457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110777621211579497213070971 166166431817369245819606457)
              ·
                refine ⟨124624823863026934364704843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166166431817369245819606457 124624823863026934364704843)
                ·
                  refine ⟨186937235794540401547057265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124624823863026934364704843 186937235794540401547057265)
                  ·
                    refine ⟨140202926845905301160292949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186937235794540401547057265 140202926845905301160292949)
                    ·
                      refine ⟨1643003048975452747972183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140202926845905301160292949 1643003048975452747972183)
                      ·
                        rfl

theorem cell23_3199737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3199737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199737 prefixEnd_3199737 := by exact prefixLift 3199737
  have htrace : WordTrace (prefixWord ++ tailWord_3199737) baseStart_3199737 baseEnd_3199737 := by
    simpa [prefixWord, tailWord_3199737, baseEnd_3199737] using wordTrace_append hprefix tailTrace_3199737
  have hstable : (prefixWord ++ tailWord_3199737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199737).length < 2 ^ (prefixWord ++ tailWord_3199737).sum := by decide
  have hdescent : baseEnd_3199737 < baseStart_3199737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199748 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3199748 : Nat := 118140960795 + 3199748 * 2 ^ 59
def prefixEnd_3199748 : Nat := 4983230072969 + 3 ^ 40 * 3199748 * 2
def baseEnd_3199748 : Nat := 1643008697262652204934633

theorem tailTrace_3199748 : CollatzResearch.WordTrace tailWord_3199748 prefixEnd_3199748 1643008697262652204934633 := by
  unfold tailWord_3199748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58352198605933472148267949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77802931474577962864357265 58352198605933472148267949)
  ·
    refine ⟨21882074477225052055600481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58352198605933472148267949 21882074477225052055600481)
    ·
      refine ⟨16411555857918789041700361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21882074477225052055600481 16411555857918789041700361)
      ·
        refine ⟨12308666893439091781275271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16411555857918789041700361 12308666893439091781275271)
        ·
          refine ⟨18463000340158637671912907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12308666893439091781275271 18463000340158637671912907)
          ·
            refine ⟨27694500510237956507869361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18463000340158637671912907 27694500510237956507869361)
            ·
              refine ⟨20770875382678467380902021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27694500510237956507869361 20770875382678467380902021)
              ·
                refine ⟨3894539134252212633919129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20770875382678467380902021 3894539134252212633919129)
                ·
                  refine ⟨2920904350689159475439347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3894539134252212633919129 2920904350689159475439347)
                  ·
                    refine ⟨4381356526033739213159021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2920904350689159475439347 4381356526033739213159021)
                    ·
                      refine ⟨1643008697262652204934633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381356526033739213159021 1643008697262652204934633)
                      ·
                        rfl

theorem cell23_3199748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3199748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199748 prefixEnd_3199748 := by exact prefixLift 3199748
  have htrace : WordTrace (prefixWord ++ tailWord_3199748) baseStart_3199748 baseEnd_3199748 := by
    simpa [prefixWord, tailWord_3199748, baseEnd_3199748] using wordTrace_append hprefix tailTrace_3199748
  have hstable : (prefixWord ++ tailWord_3199748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199748).length < 2 ^ (prefixWord ++ tailWord_3199748).sum := by decide
  have hdescent : baseEnd_3199748 < baseStart_3199748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199754 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3199754 : Nat := 118140960795 + 3199754 * 2 ^ 59
def prefixEnd_3199754 : Nat := 4983230072969 + 3 ^ 40 * 3199754 * 2
def baseEnd_3199754 : Nat := 1643011778146579181459605

theorem tailTrace_3199754 : CollatzResearch.WordTrace tailWord_3199754 prefixEnd_3199754 1643011778146579181459605 := by
  unfold tailWord_3199754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29176154012461301830313579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77803077366563471547502877 29176154012461301830313579)
  ·
    refine ⟨43764231018691952745470369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29176154012461301830313579 43764231018691952745470369)
    ·
      refine ⟨32823173264018964559102777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43764231018691952745470369 32823173264018964559102777)
      ·
        refine ⟨24617379948014223419327083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32823173264018964559102777 24617379948014223419327083)
        ·
          refine ⟨36926069922021335128990625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24617379948014223419327083 36926069922021335128990625)
          ·
            refine ⟨27694552441516001346742969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36926069922021335128990625 27694552441516001346742969)
            ·
              refine ⟨20770914331137001010057227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27694552441516001346742969 20770914331137001010057227)
              ·
                refine ⟨31156371496705501515085841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20770914331137001010057227 31156371496705501515085841)
                ·
                  refine ⟨23367278622529126136314381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31156371496705501515085841 23367278622529126136314381)
                  ·
                    refine ⟨8762729483448422301117893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23367278622529126136314381 8762729483448422301117893)
                    ·
                      refine ⟨1643011778146579181459605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8762729483448422301117893 1643011778146579181459605)
                      ·
                        rfl

theorem cell23_3199754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3199754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199754 prefixEnd_3199754 := by exact prefixLift 3199754
  have htrace : WordTrace (prefixWord ++ tailWord_3199754) baseStart_3199754 baseEnd_3199754 := by
    simpa [prefixWord, tailWord_3199754, baseEnd_3199754] using wordTrace_append hprefix tailTrace_3199754
  have hstable : (prefixWord ++ tailWord_3199754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199754).length < 2 ^ (prefixWord ++ tailWord_3199754).sum := by decide
  have hdescent : baseEnd_3199754 < baseStart_3199754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199775 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 1, 3, 2]
def baseStart_3199775 : Nat := 118140960795 + 3199775 * 2 ^ 59
def prefixEnd_3199775 : Nat := 4983230072969 + 3 ^ 40 * 3199775 * 2
def baseEnd_3199775 : Nat := 1643022561240323599297009

theorem tailTrace_3199775 : CollatzResearch.WordTrace tailWord_3199775 prefixEnd_3199775 1643022561240323599297009 := by
  unfold tailWord_3199775
  simp only [CollatzResearch.WordTrace]
  refine ⟨116705381982769127907768779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77803587988512751938512519 116705381982769127907768779)
  ·
    refine ⟨175058072974153691861653169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116705381982769127907768779 175058072974153691861653169)
    ·
      refine ⟨131293554730615268896239877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175058072974153691861653169 131293554730615268896239877)
      ·
        refine ⟨24617541511990362918044977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131293554730615268896239877 24617541511990362918044977)
        ·
          refine ⟨18463156133992772188533733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24617541511990362918044977 18463156133992772188533733)
          ·
            refine ⟨3461841775123644785350075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18463156133992772188533733 3461841775123644785350075)
            ·
              refine ⟨5192762662685467178025113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461841775123644785350075 5192762662685467178025113)
              ·
                refine ⟨3894571997014100383518835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192762662685467178025113 3894571997014100383518835)
                ·
                  refine ⟨5841857995521150575278253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894571997014100383518835 5841857995521150575278253)
                  ·
                    refine ⟨2190696748320431465729345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5841857995521150575278253 2190696748320431465729345)
                    ·
                      refine ⟨1643022561240323599297009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2190696748320431465729345 1643022561240323599297009)
                      ·
                        rfl

theorem cell23_3199775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_3199775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199775 prefixEnd_3199775 := by exact prefixLift 3199775
  have htrace : WordTrace (prefixWord ++ tailWord_3199775) baseStart_3199775 baseEnd_3199775 := by
    simpa [prefixWord, tailWord_3199775, baseEnd_3199775] using wordTrace_append hprefix tailTrace_3199775
  have hstable : (prefixWord ++ tailWord_3199775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199775).length < 2 ^ (prefixWord ++ tailWord_3199775).sum := by decide
  have hdescent : baseEnd_3199775 < baseStart_3199775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199811 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 5]
def baseStart_3199811 : Nat := 118140960795 + 3199811 * 2 ^ 59
def prefixEnd_3199811 : Nat := 4983230072969 + 3 ^ 40 * 3199811 * 2
def baseEnd_3199811 : Nat := 182560116282653939827427

theorem tailTrace_3199811 : CollatzResearch.WordTrace tailWord_3199811 prefixEnd_3199811 182560116282653939827427 := by
  unfold tailWord_3199811
  simp only [CollatzResearch.WordTrace]
  refine ⟨116706695010638706056079287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77804463340425804037386191 116706695010638706056079287)
  ·
    refine ⟨175060042515958059084118931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116706695010638706056079287 175060042515958059084118931)
    ·
      refine ⟨262590063773937088626178397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175060042515958059084118931 262590063773937088626178397)
      ·
        refine ⟨98471273915226408234816899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262590063773937088626178397 98471273915226408234816899)
        ·
          refine ⟨147706910872839612352225349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98471273915226408234816899 147706910872839612352225349)
          ·
            refine ⟨27695045788657427316042253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147706910872839612352225349 27695045788657427316042253)
            ·
              refine ⟨10385642170746535243515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27695045788657427316042253 10385642170746535243515845)
              ·
                refine ⟨1947307907014975358159221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10385642170746535243515845 1947307907014975358159221)
                ·
                  refine ⟨182560116282653939827427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947307907014975358159221 182560116282653939827427)
                  ·
                    rfl

theorem cell23_3199811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 5].length) (baseStart_3199811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199811 prefixEnd_3199811 := by exact prefixLift 3199811
  have htrace : WordTrace (prefixWord ++ tailWord_3199811) baseStart_3199811 baseEnd_3199811 := by
    simpa [prefixWord, tailWord_3199811, baseEnd_3199811] using wordTrace_append hprefix tailTrace_3199811
  have hstable : (prefixWord ++ tailWord_3199811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199811).length < 2 ^ (prefixWord ++ tailWord_3199811).sum := by decide
  have hdescent : baseEnd_3199811 < baseStart_3199811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199824 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_3199824 : Nat := 118140960795 + 3199824 * 2 ^ 59
def prefixEnd_3199824 : Nat := 4983230072969 + 3 ^ 40 * 3199824 * 2
def baseEnd_3199824 : Nat := 547682573930797969194761

theorem tailTrace_3199824 : CollatzResearch.WordTrace tailWord_3199824 prefixEnd_3199824 547682573930797969194761 := by
  unfold tailWord_3199824
  simp only [CollatzResearch.WordTrace]
  refine ⟨58353584579795804638151263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77804779439727739517535017 58353584579795804638151263)
  ·
    refine ⟨87530376869693706957226895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58353584579795804638151263 87530376869693706957226895)
    ·
      refine ⟨131295565304540560435840343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87530376869693706957226895 131295565304540560435840343)
      ·
        refine ⟨196943347956810840653760515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131295565304540560435840343 196943347956810840653760515)
        ·
          refine ⟨295415021935216260980640773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196943347956810840653760515 295415021935216260980640773)
          ·
            refine ⟨55390316612853048933870145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295415021935216260980640773 55390316612853048933870145)
            ·
              refine ⟨41542737459639786700402609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55390316612853048933870145 41542737459639786700402609)
              ·
                refine ⟨31157053094729840025301957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41542737459639786700402609 31157053094729840025301957)
                ·
                  refine ⟨5841947455261845004744117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31157053094729840025301957 5841947455261845004744117)
                  ·
                    refine ⟨547682573930797969194761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5841947455261845004744117 547682573930797969194761)
                    ·
                      rfl

theorem cell23_3199824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_3199824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199824 prefixEnd_3199824 := by exact prefixLift 3199824
  have htrace : WordTrace (prefixWord ++ tailWord_3199824) baseStart_3199824 baseEnd_3199824 := by
    simpa [prefixWord, tailWord_3199824, baseEnd_3199824] using wordTrace_append hprefix tailTrace_3199824
  have hstable : (prefixWord ++ tailWord_3199824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199824).length < 2 ^ (prefixWord ++ tailWord_3199824).sum := by decide
  have hdescent : baseEnd_3199824 < baseStart_3199824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199871 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 3, 4]
def baseStart_3199871 : Nat := 118140960795 + 3199871 * 2 ^ 59
def prefixEnd_3199871 : Nat := 4983230072969 + 3 ^ 40 * 3199871 * 2
def baseEnd_3199871 : Nat := 547690618461051741232189

theorem tailTrace_3199871 : CollatzResearch.WordTrace tailWord_3199871 prefixEnd_3199871 547690618461051741232189 := by
  unfold tailWord_3199871
  simp only [CollatzResearch.WordTrace]
  refine ⟨116708883390421336303263467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77805922260280890868842311 116708883390421336303263467)
  ·
    refine ⟨175063325085632004454895201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116708883390421336303263467 175063325085632004454895201)
    ·
      refine ⟨131297493814224003341171401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175063325085632004454895201 131297493814224003341171401)
      ·
        refine ⟨98473120360668002505878551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131297493814224003341171401 98473120360668002505878551)
        ·
          refine ⟨147709680541002003758817827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98473120360668002505878551 147709680541002003758817827)
          ·
            refine ⟨221564520811503005638226741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147709680541002003758817827 221564520811503005638226741)
            ·
              refine ⟨20771673826078406778583757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221564520811503005638226741 20771673826078406778583757)
              ·
                refine ⟨7789377684779402541968909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20771673826078406778583757 7789377684779402541968909)
                ·
                  refine ⟨2921016631792275953238341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7789377684779402541968909 2921016631792275953238341)
                  ·
                    refine ⟨547690618461051741232189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921016631792275953238341 547690618461051741232189)
                    ·
                      rfl

theorem cell23_3199871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_3199871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199871 prefixEnd_3199871 := by exact prefixLift 3199871
  have htrace : WordTrace (prefixWord ++ tailWord_3199871) baseStart_3199871 baseEnd_3199871 := by
    simpa [prefixWord, tailWord_3199871, baseEnd_3199871] using wordTrace_append hprefix tailTrace_3199871
  have hstable : (prefixWord ++ tailWord_3199871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199871).length < 2 ^ (prefixWord ++ tailWord_3199871).sum := by decide
  have hdescent : baseEnd_3199871 < baseStart_3199871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199881 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_3199881 : Nat := 118140960795 + 3199881 * 2 ^ 59
def prefixEnd_3199881 : Nat := 4983230072969 + 3 ^ 40 * 3199881 * 2
def baseEnd_3199881 : Nat := 1643076990189700184571521

theorem tailTrace_3199881 : CollatzResearch.WordTrace tailWord_3199881 prefixEnd_3199881 1643076990189700184571521 := by
  unfold tailWord_3199881
  simp only [CollatzResearch.WordTrace]
  refine ⟨116709248120385108011127497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77806165413590072007418331 116709248120385108011127497)
  ·
    refine ⟨87531936090288831008345623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116709248120385108011127497 87531936090288831008345623)
    ·
      refine ⟨131297904135433246512518435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87531936090288831008345623 131297904135433246512518435)
      ·
        refine ⟨196946856203149869768777653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131297904135433246512518435 196946856203149869768777653)
        ·
          refine ⟨18463767769045300290822905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196946856203149869768777653 18463767769045300290822905)
          ·
            refine ⟨13847825826783975218117179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18463767769045300290822905 13847825826783975218117179)
            ·
              refine ⟨20771738740175962827175769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13847825826783975218117179 20771738740175962827175769)
              ·
                refine ⟨15578804055131972120381827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20771738740175962827175769 15578804055131972120381827)
                ·
                  refine ⟨23368206082697958180572741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15578804055131972120381827 23368206082697958180572741)
                  ·
                    refine ⟨4381538640505867158857389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23368206082697958180572741 4381538640505867158857389)
                    ·
                      refine ⟨1643076990189700184571521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381538640505867158857389 1643076990189700184571521)
                      ·
                        rfl

theorem cell23_3199881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_3199881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199881 prefixEnd_3199881 := by exact prefixLift 3199881
  have htrace : WordTrace (prefixWord ++ tailWord_3199881) baseStart_3199881 baseEnd_3199881 := by
    simpa [prefixWord, tailWord_3199881, baseEnd_3199881] using wordTrace_append hprefix tailTrace_3199881
  have hstable : (prefixWord ++ tailWord_3199881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199881).length < 2 ^ (prefixWord ++ tailWord_3199881).sum := by decide
  have hdescent : baseEnd_3199881 < baseStart_3199881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199961 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_3199961 : Nat := 118140960795 + 3199961 * 2 ^ 59
def prefixEnd_3199961 : Nat := 4983230072969 + 3 ^ 40 * 3199961 * 2
def baseEnd_3199961 : Nat := 547706022880686623857051

theorem tailTrace_3199961 : CollatzResearch.WordTrace tailWord_3199961 prefixEnd_3199961 547706022880686623857051 := by
  unfold tailWord_3199961
  simp only [CollatzResearch.WordTrace]
  refine ⟨116712165960095281674039737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77808110640063521116026491 116712165960095281674039737)
  ·
    refine ⟨87534124470071461255529803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116712165960095281674039737 87534124470071461255529803)
    ·
      refine ⟨131301186705107191883294705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87534124470071461255529803 131301186705107191883294705)
      ·
        refine ⟨98475890028830393912471029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131301186705107191883294705 98475890028830393912471029)
        ·
          refine ⟨9232114690202849429294159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98475890028830393912471029 9232114690202849429294159)
          ·
            refine ⟨13848172035304274143941239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232114690202849429294159 13848172035304274143941239)
            ·
              refine ⟨20772258052956411215911859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848172035304274143941239 20772258052956411215911859)
              ·
                refine ⟨31158387079434616823867789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20772258052956411215911859 31158387079434616823867789)
                ·
                  refine ⟨11684395154787981308950421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31158387079434616823867789 11684395154787981308950421)
                  ·
                    refine ⟨547706022880686623857051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11684395154787981308950421 547706022880686623857051)
                    ·
                      rfl

theorem cell23_3199961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_3199961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3199961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3199961 prefixEnd_3199961 := by exact prefixLift 3199961
  have htrace : WordTrace (prefixWord ++ tailWord_3199961) baseStart_3199961 baseEnd_3199961 := by
    simpa [prefixWord, tailWord_3199961, baseEnd_3199961] using wordTrace_append hprefix tailTrace_3199961
  have hstable : (prefixWord ++ tailWord_3199961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199961).length < 2 ^ (prefixWord ++ tailWord_3199961).sum := by decide
  have hdescent : baseEnd_3199961 < baseStart_3199961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200008 : List Nat := [2, 1, 3, 2, 1, 4, 3, 7]
def baseStart_3200008 : Nat := 118140960795 + 3200008 * 2 ^ 59
def prefixEnd_3200008 : Nat := 4983230072969 + 3 ^ 40 * 3200008 * 2
def baseEnd_3200008 : Nat := 60857118601215599543831

theorem tailTrace_3200008 : CollatzResearch.WordTrace tailWord_3200008 prefixEnd_3200008 60857118601215599543831 := by
  unfold tailWord_3200008
  simp only [CollatzResearch.WordTrace]
  refine ⟨58356940095462504350500339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77809253460616672467333785 58356940095462504350500339)
  ·
    refine ⟨87535410143193756525750509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58356940095462504350500339 87535410143193756525750509)
    ·
      refine ⟨32825778803697658697156441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87535410143193756525750509 32825778803697658697156441)
      ·
        refine ⟨24619334102773244022867331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32825778803697658697156441 24619334102773244022867331)
        ·
          refine ⟨36929001154159866034300997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24619334102773244022867331 36929001154159866034300997)
          ·
            refine ⟨6924187716404974881431437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36929001154159866034300997 6924187716404974881431437)
            ·
              refine ⟨2596570393651865580536789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6924187716404974881431437 2596570393651865580536789)
              ·
                refine ⟨60857118601215599543831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2596570393651865580536789 60857118601215599543831)
                ·
                  rfl

theorem cell23_3200008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 7].length) (baseStart_3200008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200008 prefixEnd_3200008 := by exact prefixLift 3200008
  have htrace : WordTrace (prefixWord ++ tailWord_3200008) baseStart_3200008 baseEnd_3200008 := by
    simpa [prefixWord, tailWord_3200008, baseEnd_3200008] using wordTrace_append hprefix tailTrace_3200008
  have hstable : (prefixWord ++ tailWord_3200008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200008).length < 2 ^ (prefixWord ++ tailWord_3200008).sum := by decide
  have hdescent : baseEnd_3200008 < baseStart_3200008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200029 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_3200029 : Nat := 118140960795 + 3200029 * 2 ^ 59
def prefixEnd_3200029 : Nat := 4983230072969 + 3 ^ 40 * 3200029 * 2
def baseEnd_3200029 : Nat := 547717661775521868506947

theorem tailTrace_3200029 : CollatzResearch.WordTrace tailWord_3200029 prefixEnd_3200029 547717661775521868506947 := by
  unfold tailWord_3200029
  simp only [CollatzResearch.WordTrace]
  refine ⟨116714646123848929287515141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77809764082565952858343427 116714646123848929287515141)
  ·
    refine ⟨21883996148221674241409089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116714646123848929287515141 21883996148221674241409089)
    ·
      refine ⟨16412997111166255681056817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21883996148221674241409089 16412997111166255681056817)
      ·
        refine ⟨12309747833374691760792613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16412997111166255681056817 12309747833374691760792613)
        ·
          refine ⟨2308077718757754705148615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12309747833374691760792613 2308077718757754705148615)
          ·
            refine ⟨3462116578136632057722923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308077718757754705148615 3462116578136632057722923)
            ·
              refine ⟨5193174867204948086584385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462116578136632057722923 5193174867204948086584385)
              ·
                refine ⟨3894881150403711064938289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5193174867204948086584385 3894881150403711064938289)
                ·
                  refine ⟨2921160862802783298703717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3894881150403711064938289 2921160862802783298703717)
                  ·
                    refine ⟨547717661775521868506947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921160862802783298703717 547717661775521868506947)
                    ·
                      rfl

theorem cell23_3200029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_3200029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200029 prefixEnd_3200029 := by exact prefixLift 3200029
  have htrace : WordTrace (prefixWord ++ tailWord_3200029) baseStart_3200029 baseEnd_3200029 := by
    simpa [prefixWord, tailWord_3200029, baseEnd_3200029] using wordTrace_append hprefix tailTrace_3200029
  have hstable : (prefixWord ++ tailWord_3200029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200029).length < 2 ^ (prefixWord ++ tailWord_3200029).sum := by decide
  have hdescent : baseEnd_3200029 < baseStart_3200029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200035 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 3]
def baseStart_3200035 : Nat := 118140960795 + 3200035 * 2 ^ 59
def prefixEnd_3200035 : Nat := 4983230072969 + 3 ^ 40 * 3200035 * 2
def baseEnd_3200035 : Nat := 1643156066210492582045813

theorem tailTrace_3200035 : CollatzResearch.WordTrace tailWord_3200035 prefixEnd_3200035 1643156066210492582045813 := by
  unfold tailWord_3200035
  simp only [CollatzResearch.WordTrace]
  refine ⟨116714864961827192312233559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77809909974551461541489039 116714864961827192312233559)
  ·
    refine ⟨175072297442740788468350339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116714864961827192312233559 175072297442740788468350339)
    ·
      refine ⟨262608446164111182702525509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175072297442740788468350339 262608446164111182702525509)
      ·
        refine ⟨49239083655770846756723533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262608446164111182702525509 49239083655770846756723533)
        ·
          refine ⟨18464656370914067533771325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49239083655770846756723533 18464656370914067533771325)
          ·
            refine ⟨6924246139092775325164247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18464656370914067533771325 6924246139092775325164247)
            ·
              refine ⟨10386369208639162987746371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924246139092775325164247 10386369208639162987746371)
              ·
                refine ⟨15579553812958744481619557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10386369208639162987746371 15579553812958744481619557)
                ·
                  refine ⟨2921166339929764590303667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15579553812958744481619557 2921166339929764590303667)
                  ·
                    refine ⟨4381749509894646885455501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921166339929764590303667 4381749509894646885455501)
                    ·
                      refine ⟨1643156066210492582045813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381749509894646885455501 1643156066210492582045813)
                      ·
                        rfl

theorem cell23_3200035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_3200035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200035 prefixEnd_3200035 := by exact prefixLift 3200035
  have htrace : WordTrace (prefixWord ++ tailWord_3200035) baseStart_3200035 baseEnd_3200035 := by
    simpa [prefixWord, tailWord_3200035, baseEnd_3200035] using wordTrace_append hprefix tailTrace_3200035
  have hstable : (prefixWord ++ tailWord_3200035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200035).length < 2 ^ (prefixWord ++ tailWord_3200035).sum := by decide
  have hdescent : baseEnd_3200035 < baseStart_3200035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200052 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3200052 : Nat := 118140960795 + 3200052 * 2 ^ 59
def prefixEnd_3200052 : Nat := 4983230072969 + 3 ^ 40 * 3200052 * 2
def baseEnd_3200052 : Nat := 1643164795381619015533235

theorem tailTrace_3200052 : CollatzResearch.WordTrace tailWord_3200052 prefixEnd_3200052 1643164795381619015533235 := by
  unfold tailWord_3200052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58357742501382802107801205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77810323335177069477068273 58357742501382802107801205)
  ·
    refine ⟨5471038359504637697606363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58357742501382802107801205 5471038359504637697606363)
    ·
      refine ⟨8206557539256956546409545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5471038359504637697606363 8206557539256956546409545)
      ·
        refine ⟨6154918154442717409807159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8206557539256956546409545 6154918154442717409807159)
        ·
          refine ⟨9232377231664076114710739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154918154442717409807159 9232377231664076114710739)
          ·
            refine ⟨13848565847496114172066109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232377231664076114710739 13848565847496114172066109)
            ·
              refine ⟨5193212192811042814524791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13848565847496114172066109 5193212192811042814524791)
              ·
                refine ⟨7789818289216564221787187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193212192811042814524791 7789818289216564221787187)
                ·
                  refine ⟨11684727433824846332680781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7789818289216564221787187 11684727433824846332680781)
                  ·
                    refine ⟨4381772787684317374755293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11684727433824846332680781 4381772787684317374755293)
                    ·
                      refine ⟨1643164795381619015533235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381772787684317374755293 1643164795381619015533235)
                      ·
                        rfl

theorem cell23_3200052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3200052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200052 prefixEnd_3200052 := by exact prefixLift 3200052
  have htrace : WordTrace (prefixWord ++ tailWord_3200052) baseStart_3200052 baseEnd_3200052 := by
    simpa [prefixWord, tailWord_3200052, baseEnd_3200052] using wordTrace_append hprefix tailTrace_3200052
  have hstable : (prefixWord ++ tailWord_3200052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200052).length < 2 ^ (prefixWord ++ tailWord_3200052).sum := by decide
  have hdescent : baseEnd_3200052 < baseStart_3200052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200078 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3200078 : Nat := 118140960795 + 3200078 * 2 ^ 59
def prefixEnd_3200078 : Nat := 4983230072969 + 3 ^ 40 * 3200078 * 2
def baseEnd_3200078 : Nat := 1643178145878635913808115

theorem tailTrace_3200078 : CollatzResearch.WordTrace tailWord_3200078 prefixEnd_3200078 1643178145878635913808115 := by
  unfold tailWord_3200078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14589554162583926332006111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77810955533780940437365925 14589554162583926332006111)
  ·
    refine ⟨21884331243875889498009167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14589554162583926332006111 21884331243875889498009167)
    ·
      refine ⟨32826496865813834247013751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21884331243875889498009167 32826496865813834247013751)
      ·
        refine ⟨49239745298720751370520627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32826496865813834247013751 49239745298720751370520627)
        ·
          refine ⟨73859617948081127055780941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49239745298720751370520627 73859617948081127055780941)
          ·
            refine ⟨27697356730530422645917853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73859617948081127055780941 27697356730530422645917853)
            ·
              refine ⟨10386508773948908492219195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27697356730530422645917853 10386508773948908492219195)
              ·
                refine ⟨15579763160923362738328793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10386508773948908492219195 15579763160923362738328793)
                ·
                  refine ⟨11684822370692522053746595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15579763160923362738328793 11684822370692522053746595)
                  ·
                    refine ⟨17527233556038783080619893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11684822370692522053746595 17527233556038783080619893)
                    ·
                      refine ⟨1643178145878635913808115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17527233556038783080619893 1643178145878635913808115)
                      ·
                        rfl

theorem cell23_3200078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3200078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200078 prefixEnd_3200078 := by exact prefixLift 3200078
  have htrace : WordTrace (prefixWord ++ tailWord_3200078) baseStart_3200078 baseEnd_3200078 := by
    simpa [prefixWord, tailWord_3200078, baseEnd_3200078] using wordTrace_append hprefix tailTrace_3200078
  have hstable : (prefixWord ++ tailWord_3200078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200078).length < 2 ^ (prefixWord ++ tailWord_3200078).sum := by decide
  have hdescent : baseEnd_3200078 < baseStart_3200078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200081 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 9]
def baseStart_3200081 : Nat := 118140960795 + 3200081 * 2 ^ 59
def prefixEnd_3200081 : Nat := 4983230072969 + 3 ^ 40 * 3200081 * 2
def baseEnd_3200081 : Nat := 182575520702288822452289

theorem tailTrace_3200081 : CollatzResearch.WordTrace tailWord_3200081 prefixEnd_3200081 182575520702288822452289 := by
  unfold tailWord_3200081
  simp only [CollatzResearch.WordTrace]
  refine ⟨116716542719660542168408097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77811028479773694778938731 116716542719660542168408097)
  ·
    refine ⟨87537407039745406626306073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116716542719660542168408097 87537407039745406626306073)
    ·
      refine ⟨65653055279809054969729555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87537407039745406626306073 65653055279809054969729555)
      ·
        refine ⟨98479582919713582454594333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65653055279809054969729555 98479582919713582454594333)
        ·
          refine ⟨36929843594892593420472875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98479582919713582454594333 36929843594892593420472875)
          ·
            refine ⟨55394765392338890130709313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36929843594892593420472875 55394765392338890130709313)
            ·
              refine ⟨41546074044254167598031985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55394765392338890130709313 41546074044254167598031985)
              ·
                refine ⟨31159555533190625698523989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41546074044254167598031985 31159555533190625698523989)
                ·
                  refine ⟨182575520702288822452289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31159555533190625698523989 182575520702288822452289)
                  ·
                    rfl

theorem cell23_3200081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_3200081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200081 prefixEnd_3200081 := by exact prefixLift 3200081
  have htrace : WordTrace (prefixWord ++ tailWord_3200081) baseStart_3200081 baseEnd_3200081 := by
    simpa [prefixWord, tailWord_3200081, baseEnd_3200081] using wordTrace_append hprefix tailTrace_3200081
  have hstable : (prefixWord ++ tailWord_3200081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200081).length < 2 ^ (prefixWord ++ tailWord_3200081).sum := by decide
  have hdescent : baseEnd_3200081 < baseStart_3200081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200092 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_3200092 : Nat := 118140960795 + 3200092 * 2 ^ 59
def prefixEnd_3200092 : Nat := 4983230072969 + 3 ^ 40 * 3200092 * 2
def baseEnd_3200092 : Nat := 1643185334607798859033051

theorem tailTrace_3200092 : CollatzResearch.WordTrace tailWord_3200092 prefixEnd_3200092 1643185334607798859033051 := by
  unfold tailWord_3200092
  simp only [CollatzResearch.WordTrace]
  refine ⟨58358471961310345523529265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77811295948413794031372353 58358471961310345523529265)
  ·
    refine ⟨43768853970982759142646949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58358471961310345523529265 43768853970982759142646949)
    ·
      refine ⟨8206660119559267339246303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43768853970982759142646949 8206660119559267339246303)
      ·
        refine ⟨12309990179338901008869455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206660119559267339246303 12309990179338901008869455)
        ·
          refine ⟨18464985269008351513304183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12309990179338901008869455 18464985269008351513304183)
          ·
            refine ⟨27697477903512527269956275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18464985269008351513304183 27697477903512527269956275)
            ·
              refine ⟨41546216855268790904934413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27697477903512527269956275 41546216855268790904934413)
              ·
                refine ⟨15579831320725796589350405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41546216855268790904934413 15579831320725796589350405)
                ·
                  refine ⟨2921218372636086860503201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15579831320725796589350405 2921218372636086860503201)
                  ·
                    refine ⟨2190913779477065145377401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2921218372636086860503201 2190913779477065145377401)
                    ·
                      refine ⟨1643185334607798859033051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2190913779477065145377401 1643185334607798859033051)
                      ·
                        rfl

theorem cell23_3200092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_3200092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200092 prefixEnd_3200092 := by exact prefixLift 3200092
  have htrace : WordTrace (prefixWord ++ tailWord_3200092) baseStart_3200092 baseEnd_3200092 := by
    simpa [prefixWord, tailWord_3200092, baseEnd_3200092] using wordTrace_append hprefix tailTrace_3200092
  have hstable : (prefixWord ++ tailWord_3200092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200092).length < 2 ^ (prefixWord ++ tailWord_3200092).sum := by decide
  have hdescent : baseEnd_3200092 < baseStart_3200092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200108 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_3200108 : Nat := 118140960795 + 3200108 * 2 ^ 59
def prefixEnd_3200108 : Nat := 4983230072969 + 3 ^ 40 * 3200108 * 2
def baseEnd_3200108 : Nat := 1643193550298270796432977

theorem tailTrace_3200108 : CollatzResearch.WordTrace tailWord_3200108 prefixEnd_3200108 1643193550298270796432977 := by
  unfold tailWord_3200108
  simp only [CollatzResearch.WordTrace]
  refine ⟨58358763745281362889820489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77811684993708483853093985 58358763745281362889820489)
  ·
    refine ⟨43769072808961022167365367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58358763745281362889820489 43769072808961022167365367)
    ·
      refine ⟨65653609213441533251048051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43769072808961022167365367 65653609213441533251048051)
      ·
        refine ⟨98480413820162299876572077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65653609213441533251048051 98480413820162299876572077)
        ·
          refine ⟨36930155182560862453714529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98480413820162299876572077 36930155182560862453714529)
          ·
            refine ⟨27697616386920646840285897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36930155182560862453714529 27697616386920646840285897)
            ·
              refine ⟨20773212290190485130214423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27697616386920646840285897 20773212290190485130214423)
              ·
                refine ⟨31159818435285727695321635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20773212290190485130214423 31159818435285727695321635)
                ·
                  refine ⟨46739727652928591542982453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31159818435285727695321635 46739727652928591542982453)
                  ·
                    refine ⟨4381849467462055457154605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46739727652928591542982453 4381849467462055457154605)
                    ·
                      refine ⟨1643193550298270796432977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381849467462055457154605 1643193550298270796432977)
                      ·
                        rfl

theorem cell23_3200108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_3200108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200108 prefixEnd_3200108 := by exact prefixLift 3200108
  have htrace : WordTrace (prefixWord ++ tailWord_3200108) baseStart_3200108 baseEnd_3200108 := by
    simpa [prefixWord, tailWord_3200108, baseEnd_3200108] using wordTrace_append hprefix tailTrace_3200108
  have hstable : (prefixWord ++ tailWord_3200108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200108).length < 2 ^ (prefixWord ++ tailWord_3200108).sum := by decide
  have hdescent : baseEnd_3200108 < baseStart_3200108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200109 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_3200109 : Nat := 118140960795 + 3200109 * 2 ^ 59
def prefixEnd_3200109 : Nat := 4983230072969 + 3 ^ 40 * 3200109 * 2
def baseEnd_3200109 : Nat := 1643194063778925292520473

theorem tailTrace_3200109 : CollatzResearch.WordTrace tailWord_3200109 prefixEnd_3200109 1643194063778925292520473 := by
  unfold tailWord_3200109
  simp only [CollatzResearch.WordTrace]
  refine ⟨116717563963559102950427381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77811709309039401966951587 116717563963559102950427381)
  ·
    refine ⟨10942271621583665901602567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116717563963559102950427381 10942271621583665901602567)
    ·
      refine ⟨16413407432375498852403851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10942271621583665901602567 16413407432375498852403851)
      ·
        refine ⟨24620111148563248278605777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16413407432375498852403851 24620111148563248278605777)
        ·
          refine ⟨18465083361422436208954333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24620111148563248278605777 18465083361422436208954333)
          ·
            refine ⟨6924406260533413578357875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18465083361422436208954333 6924406260533413578357875)
            ·
              refine ⟨10386609390800120367536813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924406260533413578357875 10386609390800120367536813)
              ·
                refine ⟨3894978521550045137826305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10386609390800120367536813 3894978521550045137826305)
                ·
                  refine ⟨2921233891162533853369729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3894978521550045137826305 2921233891162533853369729)
                  ·
                    refine ⟨2190925418371900390027297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2921233891162533853369729 2190925418371900390027297)
                    ·
                      refine ⟨1643194063778925292520473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2190925418371900390027297 1643194063778925292520473)
                      ·
                        rfl

theorem cell23_3200109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_3200109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200109 prefixEnd_3200109 := by exact prefixLift 3200109
  have htrace : WordTrace (prefixWord ++ tailWord_3200109) baseStart_3200109 baseEnd_3200109 := by
    simpa [prefixWord, tailWord_3200109, baseEnd_3200109] using wordTrace_append hprefix tailTrace_3200109
  have hstable : (prefixWord ++ tailWord_3200109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200109).length < 2 ^ (prefixWord ++ tailWord_3200109).sum := by decide
  have hdescent : baseEnd_3200109 < baseStart_3200109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200128 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_3200128 : Nat := 118140960795 + 3200128 * 2 ^ 59
def prefixEnd_3200128 : Nat := 4983230072969 + 3 ^ 40 * 3200128 * 2
def baseEnd_3200128 : Nat := 547734606637120239394295

theorem tailTrace_3200128 : CollatzResearch.WordTrace tailWord_3200128 prefixEnd_3200128 547734606637120239394295 := by
  unfold tailWord_3200128
  simp only [CollatzResearch.WordTrace]
  refine ⟨58359128475245134597684519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77812171300326846130246025 58359128475245134597684519)
  ·
    refine ⟨87538692712867701896526779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58359128475245134597684519 87538692712867701896526779)
    ·
      refine ⟨131308039069301552844790169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87538692712867701896526779 131308039069301552844790169)
      ·
        refine ⟨98481029301976164633592627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131308039069301552844790169 98481029301976164633592627)
        ·
          refine ⟨147721543952964246950388941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98481029301976164633592627 147721543952964246950388941)
          ·
            refine ⟨55395578982361592606395853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147721543952964246950388941 55395578982361592606395853)
            ·
              refine ⟨20773342118385597227398445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55395578982361592606395853 20773342118385597227398445)
              ·
                refine ⟨7790003294394598960274417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20773342118385597227398445 7790003294394598960274417)
                ·
                  refine ⟨5842502470795949220205813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7790003294394598960274417 5842502470795949220205813)
                  ·
                    refine ⟨547734606637120239394295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5842502470795949220205813 547734606637120239394295)
                    ·
                      rfl

theorem cell23_3200128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_3200128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200128 prefixEnd_3200128 := by exact prefixLift 3200128
  have htrace : WordTrace (prefixWord ++ tailWord_3200128) baseStart_3200128 baseEnd_3200128 := by
    simpa [prefixWord, tailWord_3200128, baseEnd_3200128] using wordTrace_append hprefix tailTrace_3200128
  have hstable : (prefixWord ++ tailWord_3200128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200128).length < 2 ^ (prefixWord ++ tailWord_3200128).sum := by decide
  have hdescent : baseEnd_3200128 < baseStart_3200128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200138 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3200138 : Nat := 118140960795 + 3200138 * 2 ^ 59
def prefixEnd_3200138 : Nat := 4983230072969 + 3 ^ 40 * 3200138 * 2
def baseEnd_3200138 : Nat := 1643208954717905679057839

theorem tailTrace_3200138 : CollatzResearch.WordTrace tailWord_3200138 prefixEnd_3200138 1643208954717905679057839 := by
  unfold tailWord_3200138
  simp only [CollatzResearch.WordTrace]
  refine ⟨29179655420113510225808267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77812414453636027268822045 29179655420113510225808267)
  ·
    refine ⟨43769483130170265338712401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29179655420113510225808267 43769483130170265338712401)
    ·
      refine ⟨32827112347627699004034301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43769483130170265338712401 32827112347627699004034301)
      ·
        refine ⟨12310167130360387126512863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32827112347627699004034301 12310167130360387126512863)
        ·
          refine ⟨18465250695540580689769295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310167130360387126512863 18465250695540580689769295)
          ·
            refine ⟨27697876043310871034653943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465250695540580689769295 27697876043310871034653943)
            ·
              refine ⟨41546814064966306551980915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27697876043310871034653943 41546814064966306551980915)
              ·
                refine ⟨62320221097449459827971373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41546814064966306551980915 62320221097449459827971373)
                ·
                  refine ⟨23370082911543547435489265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62320221097449459827971373 23370082911543547435489265)
                  ·
                    refine ⟨17527562183657660576616949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23370082911543547435489265 17527562183657660576616949)
                    ·
                      refine ⟨1643208954717905679057839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17527562183657660576616949 1643208954717905679057839)
                      ·
                        rfl

theorem cell23_3200138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3200138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200138 prefixEnd_3200138 := by exact prefixLift 3200138
  have htrace : WordTrace (prefixWord ++ tailWord_3200138) baseStart_3200138 baseEnd_3200138 := by
    simpa [prefixWord, tailWord_3200138, baseEnd_3200138] using wordTrace_append hprefix tailTrace_3200138
  have hstable : (prefixWord ++ tailWord_3200138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200138).length < 2 ^ (prefixWord ++ tailWord_3200138).sum := by decide
  have hdescent : baseEnd_3200138 < baseStart_3200138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200165 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_3200165 : Nat := 118140960795 + 3200165 * 2 ^ 59
def prefixEnd_3200165 : Nat := 4983230072969 + 3 ^ 40 * 3200165 * 2
def baseEnd_3200165 : Nat := 1643222818695577073420215

theorem tailTrace_3200165 : CollatzResearch.WordTrace tailWord_3200165 prefixEnd_3200165 1643222818695577073420215 := by
  unfold tailWord_3200165
  simp only [CollatzResearch.WordTrace]
  refine ⟨116719606451356224514465949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77813070967570816342977299 116719606451356224514465949)
  ·
    refine ⟨43769852419258584192924731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116719606451356224514465949 43769852419258584192924731)
    ·
      refine ⟨65654778628887876289387097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43769852419258584192924731 65654778628887876289387097)
      ·
        refine ⟨49241083971665907217040323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65654778628887876289387097 49241083971665907217040323)
        ·
          refine ⟨73861625957498860825560485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49241083971665907217040323 73861625957498860825560485)
          ·
            refine ⟨13849054867031036404792591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73861625957498860825560485 13849054867031036404792591)
            ·
              refine ⟨20773582300546554607188887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849054867031036404792591 20773582300546554607188887)
              ·
                refine ⟨31160373450819831910783331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20773582300546554607188887 31160373450819831910783331)
                ·
                  refine ⟨46740560176229747866174997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31160373450819831910783331 46740560176229747866174997)
                  ·
                    refine ⟨2190963758260769431226953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46740560176229747866174997 2190963758260769431226953)
                    ·
                      refine ⟨1643222818695577073420215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2190963758260769431226953 1643222818695577073420215)
                      ·
                        rfl

theorem cell23_3200165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_3200165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200165 prefixEnd_3200165 := by exact prefixLift 3200165
  have htrace : WordTrace (prefixWord ++ tailWord_3200165) baseStart_3200165 baseEnd_3200165 := by
    simpa [prefixWord, tailWord_3200165, baseEnd_3200165] using wordTrace_append hprefix tailTrace_3200165
  have hstable : (prefixWord ++ tailWord_3200165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200165).length < 2 ^ (prefixWord ++ tailWord_3200165).sum := by decide
  have hdescent : baseEnd_3200165 < baseStart_3200165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200185 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3200185 : Nat := 118140960795 + 3200185 * 2 ^ 59
def prefixEnd_3200185 : Nat := 4983230072969 + 3 ^ 40 * 3200185 * 2
def baseEnd_3200185 : Nat := 1643233088308666995170123

theorem tailTrace_3200185 : CollatzResearch.WordTrace tailWord_3200185 prefixEnd_3200185 1643233088308666995170123 := by
  unfold tailWord_3200185
  simp only [CollatzResearch.WordTrace]
  refine ⟨116720335911283767930194009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77813557274189178620129339 116720335911283767930194009)
  ·
    refine ⟨87540251933462825947645507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116720335911283767930194009 87540251933462825947645507)
    ·
      refine ⟨131310377900194238921468261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87540251933462825947645507 131310377900194238921468261)
      ·
        refine ⟨24620695856286419797775299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131310377900194238921468261 24620695856286419797775299)
        ·
          refine ⟨36931043784429629696662949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24620695856286419797775299 36931043784429629696662949)
          ·
            refine ⟨6924570709580555568124303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36931043784429629696662949 6924570709580555568124303)
            ·
              refine ⟨10386856064370833352186455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924570709580555568124303 10386856064370833352186455)
              ·
                refine ⟨15580284096556250028279683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10386856064370833352186455 15580284096556250028279683)
                ·
                  refine ⟨23370426144834375042419525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15580284096556250028279683 23370426144834375042419525)
                  ·
                    refine ⟨4381954902156445320453661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23370426144834375042419525 4381954902156445320453661)
                    ·
                      refine ⟨1643233088308666995170123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4381954902156445320453661 1643233088308666995170123)
                      ·
                        rfl

theorem cell23_3200185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3200185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200185 prefixEnd_3200185 := by exact prefixLift 3200185
  have htrace : WordTrace (prefixWord ++ tailWord_3200185) baseStart_3200185 baseEnd_3200185 := by
    simpa [prefixWord, tailWord_3200185, baseEnd_3200185] using wordTrace_append hprefix tailTrace_3200185
  have hstable : (prefixWord ++ tailWord_3200185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200185).length < 2 ^ (prefixWord ++ tailWord_3200185).sum := by decide
  have hdescent : baseEnd_3200185 < baseStart_3200185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200228 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_3200228 : Nat := 118140960795 + 3200228 * 2 ^ 59
def prefixEnd_3200228 : Nat := 4983230072969 + 3 ^ 40 * 3200228 * 2
def baseEnd_3200228 : Nat := 1643255167976810326932425

theorem tailTrace_3200228 : CollatzResearch.WordTrace tailWord_3200228 prefixEnd_3200228 1643255167976810326932425 := by
  unfold tailWord_3200228
  simp only [CollatzResearch.WordTrace]
  refine ⟨58360952125063993137004669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77814602833418657516006225 58360952125063993137004669)
  ·
    refine ⟨21885357046898997426376751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58360952125063993137004669 21885357046898997426376751)
    ·
      refine ⟨32828035570348496139565127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885357046898997426376751 32828035570348496139565127)
      ·
        refine ⟨49242053355522744209347691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32828035570348496139565127 49242053355522744209347691)
        ·
          refine ⟨73863080033284116314021537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49242053355522744209347691 73863080033284116314021537)
          ·
            refine ⟨55397310024963087235516153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73863080033284116314021537 55397310024963087235516153)
            ·
              refine ⟨41547982518722315426637115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55397310024963087235516153 41547982518722315426637115)
              ·
                refine ⟨62321973778083473139955673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41547982518722315426637115 62321973778083473139955673)
                ·
                  refine ⟨46741480333562604854966755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62321973778083473139955673 46741480333562604854966755)
                  ·
                    refine ⟨70112220500343907282450133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46741480333562604854966755 70112220500343907282450133)
                    ·
                      refine ⟨1643255167976810326932425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70112220500343907282450133 1643255167976810326932425)
                      ·
                        rfl

theorem cell23_3200228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_3200228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200228 prefixEnd_3200228 := by exact prefixLift 3200228
  have htrace : WordTrace (prefixWord ++ tailWord_3200228) baseStart_3200228 baseEnd_3200228 := by
    simpa [prefixWord, tailWord_3200228, baseEnd_3200228] using wordTrace_append hprefix tailTrace_3200228
  have hstable : (prefixWord ++ tailWord_3200228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200228).length < 2 ^ (prefixWord ++ tailWord_3200228).sum := by decide
  have hdescent : baseEnd_3200228 < baseStart_3200228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200232 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3200232 : Nat := 118140960795 + 3200232 * 2 ^ 59
def prefixEnd_3200232 : Nat := 4983230072969 + 3 ^ 40 * 3200232 * 2
def baseEnd_3200232 : Nat := 1643257221899428311282407

theorem tailTrace_3200232 : CollatzResearch.WordTrace tailWord_3200232 prefixEnd_3200232 1643257221899428311282407 := by
  unfold tailWord_3200232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58361025071056747478577475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77814700094742329971436633 58361025071056747478577475)
  ·
    refine ⟨87541537606585121217866213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58361025071056747478577475 87541537606585121217866213)
    ·
      refine ⟨16414038301234710228349915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87541537606585121217866213 16414038301234710228349915)
      ·
        refine ⟨24621057451852065342524873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16414038301234710228349915 24621057451852065342524873)
        ·
          refine ⟨18465793088889049006893655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24621057451852065342524873 18465793088889049006893655)
          ·
            refine ⟨27698689633333573510340483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18465793088889049006893655 27698689633333573510340483)
            ·
              refine ⟨41548034450000360265510725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27698689633333573510340483 41548034450000360265510725)
              ·
                refine ⟨7790256459375067549783261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41548034450000360265510725 7790256459375067549783261)
                ·
                  refine ⟨2921346172265650331168723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7790256459375067549783261 2921346172265650331168723)
                  ·
                    refine ⟨4382019258398475496753085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921346172265650331168723 4382019258398475496753085)
                    ·
                      refine ⟨1643257221899428311282407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382019258398475496753085 1643257221899428311282407)
                      ·
                        rfl

theorem cell23_3200232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3200232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200232 prefixEnd_3200232 := by exact prefixLift 3200232
  have htrace : WordTrace (prefixWord ++ tailWord_3200232) baseStart_3200232 baseEnd_3200232 := by
    simpa [prefixWord, tailWord_3200232, baseEnd_3200232] using wordTrace_append hprefix tailTrace_3200232
  have hstable : (prefixWord ++ tailWord_3200232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200232).length < 2 ^ (prefixWord ++ tailWord_3200232).sum := by decide
  have hdescent : baseEnd_3200232 < baseStart_3200232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200235 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 1, 5]
def baseStart_3200235 : Nat := 118140960795 + 3200235 * 2 ^ 59
def prefixEnd_3200235 : Nat := 4983230072969 + 3 ^ 40 * 3200235 * 2
def baseEnd_3200235 : Nat := 547752920780463933181631

theorem tailTrace_3200235 : CollatzResearch.WordTrace tailWord_3200235 prefixEnd_3200235 547752920780463933181631 := by
  unfold tailWord_3200235
  simp only [CollatzResearch.WordTrace]
  refine ⟨116722159561102626469514159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77814773040735084313009439 116722159561102626469514159)
  ·
    refine ⟨175083239341653939704271239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116722159561102626469514159 175083239341653939704271239)
    ·
      refine ⟨262624859012480909556406859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175083239341653939704271239 262624859012480909556406859)
      ·
        refine ⟨393937288518721364334610289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262624859012480909556406859 393937288518721364334610289)
        ·
          refine ⟨295452966389041023250957717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393937288518721364334610289 295452966389041023250957717)
          ·
            refine ⟨13849357799486297964888643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 295452966389041023250957717 13849357799486297964888643)
            ·
              refine ⟨20774036699229446947332965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849357799486297964888643 20774036699229446947332965)
              ·
                refine ⟨3895131881105521302624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20774036699229446947332965 3895131881105521302624931)
                ·
                  refine ⟨5842697821658281953937397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895131881105521302624931 5842697821658281953937397)
                  ·
                    refine ⟨547752920780463933181631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5842697821658281953937397 547752920780463933181631)
                    ·
                      rfl

theorem cell23_3200235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 5].length) (baseStart_3200235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200235 prefixEnd_3200235 := by exact prefixLift 3200235
  have htrace : WordTrace (prefixWord ++ tailWord_3200235) baseStart_3200235 baseEnd_3200235 := by
    simpa [prefixWord, tailWord_3200235, baseEnd_3200235] using wordTrace_append hprefix tailTrace_3200235
  have hstable : (prefixWord ++ tailWord_3200235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200235).length < 2 ^ (prefixWord ++ tailWord_3200235).sum := by decide
  have hdescent : baseEnd_3200235 < baseStart_3200235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200265 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_3200265 : Nat := 118140960795 + 3200265 * 2 ^ 59
def prefixEnd_3200265 : Nat := 4983230072969 + 3 ^ 40 * 3200265 * 2
def baseEnd_3200265 : Nat := 547758055587008894056585

theorem tailTrace_3200265 : CollatzResearch.WordTrace tailWord_3200265 prefixEnd_3200265 547758055587008894056585 := by
  unfold tailWord_3200265
  simp only [CollatzResearch.WordTrace]
  refine ⟨116723253750993941593106249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77815502500662627728737499 116723253750993941593106249)
  ·
    refine ⟨87542440313245456194829687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116723253750993941593106249 87542440313245456194829687)
    ·
      refine ⟨131313660469868184292244531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87542440313245456194829687 131313660469868184292244531)
      ·
        refine ⟨196970490704802276438366797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131313660469868184292244531 196970490704802276438366797)
        ·
          refine ⟨73863934014300853664387549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196970490704802276438366797 73863934014300853664387549)
          ·
            refine ⟨27698975255362820124145331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73863934014300853664387549 27698975255362820124145331)
            ·
              refine ⟨41548462883044230186217997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27698975255362820124145331 41548462883044230186217997)
              ·
                refine ⟨15580673581141586319831749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41548462883044230186217997 15580673581141586319831749)
                ·
                  refine ⟨2921376296464047434968453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15580673581141586319831749 2921376296464047434968453)
                  ·
                    refine ⟨547758055587008894056585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921376296464047434968453 547758055587008894056585)
                    ·
                      rfl

theorem cell23_3200265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_3200265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200265 prefixEnd_3200265 := by exact prefixLift 3200265
  have htrace : WordTrace (prefixWord ++ tailWord_3200265) baseStart_3200265 baseEnd_3200265 := by
    simpa [prefixWord, tailWord_3200265, baseEnd_3200265] using wordTrace_append hprefix tailTrace_3200265
  have hstable : (prefixWord ++ tailWord_3200265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200265).length < 2 ^ (prefixWord ++ tailWord_3200265).sum := by decide
  have hdescent : baseEnd_3200265 < baseStart_3200265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200292 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3200292 : Nat := 118140960795 + 3200292 * 2 ^ 59
def prefixEnd_3200292 : Nat := 4983230072969 + 3 ^ 40 * 3200292 * 2
def baseEnd_3200292 : Nat := 1643288030738698076532131

theorem tailTrace_3200292 : CollatzResearch.WordTrace tailWord_3200292 prefixEnd_3200292 1643288030738698076532131 := by
  unfold tailWord_3200292
  simp only [CollatzResearch.WordTrace]
  refine ⟨58362119260948062602169565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77816159014597416802892753 58362119260948062602169565)
  ·
    refine ⟨21885794722855523475813587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58362119260948062602169565 21885794722855523475813587)
    ·
      refine ⟨32828692084283285213720381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885794722855523475813587 32828692084283285213720381)
      ·
        refine ⟨12310759531606231955145143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32828692084283285213720381 12310759531606231955145143)
        ·
          refine ⟨18466139297409347932717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310759531606231955145143 18466139297409347932717715)
          ·
            refine ⟨27699208946114021899076573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18466139297409347932717715 27699208946114021899076573)
            ·
              refine ⟨10387203354792758212153715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27699208946114021899076573 10387203354792758212153715)
              ·
                refine ⟨15580805032189137318230573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387203354792758212153715 15580805032189137318230573)
                ·
                  refine ⟨5842801887070926494336465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15580805032189137318230573 5842801887070926494336465)
                  ·
                    refine ⟨4382101415303194870752349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5842801887070926494336465 4382101415303194870752349)
                    ·
                      refine ⟨1643288030738698076532131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382101415303194870752349 1643288030738698076532131)
                      ·
                        rfl

theorem cell23_3200292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3200292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200292 prefixEnd_3200292 := by exact prefixLift 3200292
  have htrace : WordTrace (prefixWord ++ tailWord_3200292) baseStart_3200292 baseEnd_3200292 := by
    simpa [prefixWord, tailWord_3200292, baseEnd_3200292] using wordTrace_append hprefix tailTrace_3200292
  have hstable : (prefixWord ++ tailWord_3200292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200292).length < 2 ^ (prefixWord ++ tailWord_3200292).sum := by decide
  have hdescent : baseEnd_3200292 < baseStart_3200292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200317 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3200317 : Nat := 118140960795 + 3200317 * 2 ^ 59
def prefixEnd_3200317 : Nat := 4983230072969 + 3 ^ 40 * 3200317 * 2
def baseEnd_3200317 : Nat := 1643300867755060478719517

theorem tailTrace_3200317 : CollatzResearch.WordTrace tailWord_3200317 prefixEnd_3200317 1643300867755060478719517 := by
  unfold tailWord_3200317
  simp only [CollatzResearch.WordTrace]
  refine ⟨116725150346805554473999205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77816766897870369649332803 116725150346805554473999205)
  ·
    refine ⟨21885965690026041463874851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116725150346805554473999205 21885965690026041463874851)
    ·
      refine ⟨32828948535039062195812277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885965690026041463874851 32828948535039062195812277)
      ·
        refine ⟨3077713925159912080857401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32828948535039062195812277 3077713925159912080857401)
        ·
          refine ⟨2308285443869934060643051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3077713925159912080857401 2308285443869934060643051)
          ·
            refine ⟨3462428165804901090964577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308285443869934060643051 3462428165804901090964577)
            ·
              refine ⟨2596821124353675818223433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462428165804901090964577 2596821124353675818223433)
              ·
                refine ⟨1947615843265256863667575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596821124353675818223433 1947615843265256863667575)
                ·
                  refine ⟨2921423764897885295501363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947615843265256863667575 2921423764897885295501363)
                  ·
                    refine ⟨4382135647346827943252045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921423764897885295501363 4382135647346827943252045)
                    ·
                      refine ⟨1643300867755060478719517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382135647346827943252045 1643300867755060478719517)
                      ·
                        rfl

theorem cell23_3200317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3200317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200317 prefixEnd_3200317 := by exact prefixLift 3200317
  have htrace : WordTrace (prefixWord ++ tailWord_3200317) baseStart_3200317 baseEnd_3200317 := by
    simpa [prefixWord, tailWord_3200317, baseEnd_3200317] using wordTrace_append hprefix tailTrace_3200317
  have hstable : (prefixWord ++ tailWord_3200317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200317).length < 2 ^ (prefixWord ++ tailWord_3200317).sum := by decide
  have hdescent : baseEnd_3200317 < baseStart_3200317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200373 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3200373 : Nat := 118140960795 + 3200373 * 2 ^ 59
def prefixEnd_3200373 : Nat := 4983230072969 + 3 ^ 40 * 3200373 * 2
def baseEnd_3200373 : Nat := 1643329622671712259619259

theorem tailTrace_3200373 : CollatzResearch.WordTrace tailWord_3200373 prefixEnd_3200373 1643329622671712259619259 := by
  unfold tailWord_3200373
  simp only [CollatzResearch.WordTrace]
  refine ⟨116727192834602676038037773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77818128556401784025358515 116727192834602676038037773)
  ·
    refine ⟨43772697312976003514264165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116727192834602676038037773 43772697312976003514264165)
    ·
      refine ⟨8207380746183000658924531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43772697312976003514264165 8207380746183000658924531)
      ·
        refine ⟨12311071119274500988386797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207380746183000658924531 12311071119274500988386797)
        ·
          refine ⟨4616651669727937870645049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12311071119274500988386797 4616651669727937870645049)
          ·
            refine ⟨3462488752295953402983787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616651669727937870645049 3462488752295953402983787)
            ·
              refine ⟨5193733128443930104475681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462488752295953402983787 5193733128443930104475681)
              ·
                refine ⟨3895299846332947578356761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5193733128443930104475681 3895299846332947578356761)
                ·
                  refine ⟨2921474884749710683767571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3895299846332947578356761 2921474884749710683767571)
                  ·
                    refine ⟨4382212327124566025651357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921474884749710683767571 4382212327124566025651357)
                    ·
                      refine ⟨1643329622671712259619259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382212327124566025651357 1643329622671712259619259)
                      ·
                        rfl

theorem cell23_3200373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3200373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200373 prefixEnd_3200373 := by exact prefixLift 3200373
  have htrace : WordTrace (prefixWord ++ tailWord_3200373) baseStart_3200373 baseEnd_3200373 := by
    simpa [prefixWord, tailWord_3200373, baseEnd_3200373] using wordTrace_append hprefix tailTrace_3200373
  have hstable : (prefixWord ++ tailWord_3200373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200373).length < 2 ^ (prefixWord ++ tailWord_3200373).sum := by decide
  have hdescent : baseEnd_3200373 < baseStart_3200373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200375 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3200375 : Nat := 118140960795 + 3200375 * 2 ^ 59
def prefixEnd_3200375 : Nat := 4983230072969 + 3 ^ 40 * 3200375 * 2
def baseEnd_3200375 : Nat := 1643330649633021251794249

theorem tailTrace_3200375 : CollatzResearch.WordTrace tailWord_3200375 prefixEnd_3200375 1643330649633021251794249 := by
  unfold tailWord_3200375
  simp only [CollatzResearch.WordTrace]
  refine ⟨116727265780595430379610579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77818177187063620253073719 116727265780595430379610579)
  ·
    refine ⟨175090898670893145569415869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116727265780595430379610579 175090898670893145569415869)
    ·
      refine ⟨65659087001584929588530951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175090898670893145569415869 65659087001584929588530951)
      ·
        refine ⟨98488630502377394382796427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65659087001584929588530951 98488630502377394382796427)
        ·
          refine ⟨147732945753566091574194641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98488630502377394382796427 147732945753566091574194641)
          ·
            refine ⟨110799709315174568680645981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147732945753566091574194641 110799709315174568680645981)
            ·
              refine ⟨41549890993190463255242243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110799709315174568680645981 41549890993190463255242243)
              ·
                refine ⟨62324836489785694882863365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41549890993190463255242243 62324836489785694882863365)
                ·
                  refine ⟨11685906841834817790536881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62324836489785694882863365 11685906841834817790536881)
                  ·
                    refine ⟨8764430131376113342902661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11685906841834817790536881 8764430131376113342902661)
                    ·
                      refine ⟨1643330649633021251794249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8764430131376113342902661 1643330649633021251794249)
                      ·
                        rfl

theorem cell23_3200375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3200375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200375 prefixEnd_3200375 := by exact prefixLift 3200375
  have htrace : WordTrace (prefixWord ++ tailWord_3200375) baseStart_3200375 baseEnd_3200375 := by
    simpa [prefixWord, tailWord_3200375, baseEnd_3200375] using wordTrace_append hprefix tailTrace_3200375
  have hstable : (prefixWord ++ tailWord_3200375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200375).length < 2 ^ (prefixWord ++ tailWord_3200375).sum := by decide
  have hdescent : baseEnd_3200375 < baseStart_3200375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200379 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 4, 2, 2]
def baseStart_3200379 : Nat := 118140960795 + 3200379 * 2 ^ 59
def prefixEnd_3200379 : Nat := 4983230072969 + 3 ^ 40 * 3200379 * 2
def baseEnd_3200379 : Nat := 1643332703555639236144231

theorem tailTrace_3200379 : CollatzResearch.WordTrace tailWord_3200379 prefixEnd_3200379 1643332703555639236144231 := by
  unfold tailWord_3200379
  simp only [CollatzResearch.WordTrace]
  refine ⟨116727411672580939062756191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77818274448387292708504127 116727411672580939062756191)
  ·
    refine ⟨175091117508871408594134287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116727411672580939062756191 175091117508871408594134287)
    ·
      refine ⟨262636676263307112891201431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175091117508871408594134287 262636676263307112891201431)
      ·
        refine ⟨393955014394960669336802147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262636676263307112891201431 393955014394960669336802147)
        ·
          refine ⟨590932521592441004005203221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393955014394960669336802147 590932521592441004005203221)
          ·
            refine ⟨27699961949645672062743901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 590932521592441004005203221 27699961949645672062743901)
            ·
              refine ⟨10387485731117127023528963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27699961949645672062743901 10387485731117127023528963)
              ·
                refine ⟨15581228596675690535293445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387485731117127023528963 15581228596675690535293445)
                ·
                  refine ⟨2921480361876691975367521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15581228596675690535293445 2921480361876691975367521)
                  ·
                    refine ⟨2191110271407518981525641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2921480361876691975367521 2191110271407518981525641)
                    ·
                      refine ⟨1643332703555639236144231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191110271407518981525641 1643332703555639236144231)
                      ·
                        rfl

theorem cell23_3200379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2, 2].length) (baseStart_3200379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200379 prefixEnd_3200379 := by exact prefixLift 3200379
  have htrace : WordTrace (prefixWord ++ tailWord_3200379) baseStart_3200379 baseEnd_3200379 := by
    simpa [prefixWord, tailWord_3200379, baseEnd_3200379] using wordTrace_append hprefix tailTrace_3200379
  have hstable : (prefixWord ++ tailWord_3200379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200379).length < 2 ^ (prefixWord ++ tailWord_3200379).sum := by decide
  have hdescent : baseEnd_3200379 < baseStart_3200379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200392 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3200392 : Nat := 118140960795 + 3200392 * 2 ^ 59
def prefixEnd_3200392 : Nat := 4983230072969 + 3 ^ 40 * 3200392 * 2
def baseEnd_3200392 : Nat := 1643339378804147685281671

theorem tailTrace_3200392 : CollatzResearch.WordTrace tailWord_3200392 prefixEnd_3200392 1643339378804147685281671 := by
  unfold tailWord_3200392
  simp only [CollatzResearch.WordTrace]
  refine ⟨58363942910766921141489715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77818590547689228188652953 58363942910766921141489715)
  ·
    refine ⟨87545914366150381712234573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58363942910766921141489715 87545914366150381712234573)
    ·
      refine ⟨32829717887306393142087965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87545914366150381712234573 32829717887306393142087965)
      ·
        refine ⟨12311144207739897428282987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32829717887306393142087965 12311144207739897428282987)
        ·
          refine ⟨18466716311609846142424481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311144207739897428282987 18466716311609846142424481)
          ·
            refine ⟨13850037233707384606818361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18466716311609846142424481 13850037233707384606818361)
            ·
              refine ⟨10387527925280538455113771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13850037233707384606818361 10387527925280538455113771)
              ·
                refine ⟨15581291887920807682670657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387527925280538455113771 15581291887920807682670657)
                ·
                  refine ⟨11685968915940605762002993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15581291887920807682670657 11685968915940605762002993)
                  ·
                    refine ⟨8764476686955454321502245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11685968915940605762002993 8764476686955454321502245)
                    ·
                      refine ⟨1643339378804147685281671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8764476686955454321502245 1643339378804147685281671)
                      ·
                        rfl

theorem cell23_3200392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3200392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200392 prefixEnd_3200392 := by exact prefixLift 3200392
  have htrace : WordTrace (prefixWord ++ tailWord_3200392) baseStart_3200392 baseEnd_3200392 := by
    simpa [prefixWord, tailWord_3200392, baseEnd_3200392] using wordTrace_append hprefix tailTrace_3200392
  have hstable : (prefixWord ++ tailWord_3200392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200392).length < 2 ^ (prefixWord ++ tailWord_3200392).sum := by decide
  have hdescent : baseEnd_3200392 < baseStart_3200392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200465 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3200465 : Nat := 118140960795 + 3200465 * 2 ^ 59
def prefixEnd_3200465 : Nat := 4983230072969 + 3 ^ 40 * 3200465 * 2
def baseEnd_3200465 : Nat := 1643376862891925899668835

theorem tailTrace_3200465 : CollatzResearch.WordTrace tailWord_3200465 prefixEnd_3200465 1643376862891925899668835 := by
  unfold tailWord_3200465
  simp only [CollatzResearch.WordTrace]
  refine ⟨116730548350269375750386849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77820365566846250500257899 116730548350269375750386849)
  ·
    refine ⟨87547911262702031812790137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116730548350269375750386849 87547911262702031812790137)
    ·
      refine ⟨65660933447026523859592603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87547911262702031812790137 65660933447026523859592603)
      ·
        refine ⟨98491400170539785789388905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65660933447026523859592603 98491400170539785789388905)
        ·
          refine ⟨73868550127904839342041679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98491400170539785789388905 73868550127904839342041679)
          ·
            refine ⟨110802825191857259013062519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73868550127904839342041679 110802825191857259013062519)
            ·
              refine ⟨166204237787785888519593779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110802825191857259013062519 166204237787785888519593779)
              ·
                refine ⟨249306356681678832779390669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166204237787785888519593779 249306356681678832779390669)
                ·
                  refine ⟨93489883755629562292271501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249306356681678832779390669 93489883755629562292271501)
                  ·
                    refine ⟨35058706408361085859601813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93489883755629562292271501 35058706408361085859601813)
                    ·
                      refine ⟨1643376862891925899668835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35058706408361085859601813 1643376862891925899668835)
                      ·
                        rfl

theorem cell23_3200465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3200465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200465 prefixEnd_3200465 := by exact prefixLift 3200465
  have htrace : WordTrace (prefixWord ++ tailWord_3200465) baseStart_3200465 baseEnd_3200465 := by
    simpa [prefixWord, tailWord_3200465, baseEnd_3200465] using wordTrace_append hprefix tailTrace_3200465
  have hstable : (prefixWord ++ tailWord_3200465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200465).length < 2 ^ (prefixWord ++ tailWord_3200465).sum := by decide
  have hdescent : baseEnd_3200465 < baseStart_3200465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200469 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3200469 : Nat := 118140960795 + 3200469 * 2 ^ 59
def prefixEnd_3200469 : Nat := 4983230072969 + 3 ^ 40 * 3200469 * 2
def baseEnd_3200469 : Nat := 1643378916814543884018817

theorem tailTrace_3200469 : CollatzResearch.WordTrace tailWord_3200469 prefixEnd_3200469 1643378916814543884018817 := by
  unfold tailWord_3200469
  simp only [CollatzResearch.WordTrace]
  refine ⟨116730694242254884433532461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77820462828169922955688307 116730694242254884433532461)
  ·
    refine ⟨43774010340845581662574673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116730694242254884433532461 43774010340845581662574673)
    ·
      refine ⟨32830507755634186246931005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43774010340845581662574673 32830507755634186246931005)
      ·
        refine ⟨12311440408362819842599127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32830507755634186246931005 12311440408362819842599127)
        ·
          refine ⟨18467160612544229763898691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311440408362819842599127 18467160612544229763898691)
          ·
            refine ⟨27700740918816344645848037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18467160612544229763898691 27700740918816344645848037)
            ·
              refine ⟨5193888922278064621096507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27700740918816344645848037 5193888922278064621096507)
              ·
                refine ⟨7790833383417096931644761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193888922278064621096507 7790833383417096931644761)
                ·
                  refine ⟨5843125037562822698733571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7790833383417096931644761 5843125037562822698733571)
                  ·
                    refine ⟨8764687556344234048100357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5843125037562822698733571 8764687556344234048100357)
                    ·
                      refine ⟨1643378916814543884018817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8764687556344234048100357 1643378916814543884018817)
                      ·
                        rfl

theorem cell23_3200469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3200469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200469 prefixEnd_3200469 := by exact prefixLift 3200469
  have htrace : WordTrace (prefixWord ++ tailWord_3200469) baseStart_3200469 baseEnd_3200469 := by
    simpa [prefixWord, tailWord_3200469, baseEnd_3200469] using wordTrace_append hprefix tailTrace_3200469
  have hstable : (prefixWord ++ tailWord_3200469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200469).length < 2 ^ (prefixWord ++ tailWord_3200469).sum := by decide
  have hdescent : baseEnd_3200469 < baseStart_3200469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200472 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3200472 : Nat := 118140960795 + 3200472 * 2 ^ 59
def prefixEnd_3200472 : Nat := 4983230072969 + 3 ^ 40 * 3200472 * 2
def baseEnd_3200472 : Nat := 1643380457256507372281303

theorem tailTrace_3200472 : CollatzResearch.WordTrace tailWord_3200472 prefixEnd_3200472 1643380457256507372281303 := by
  unfold tailWord_3200472
  simp only [CollatzResearch.WordTrace]
  refine ⟨58365401830622007972945835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77820535774162677297261113 58365401830622007972945835)
  ·
    refine ⟨87548102745933011959418753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58365401830622007972945835 87548102745933011959418753)
    ·
      refine ⟨65661077059449758969564065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87548102745933011959418753 65661077059449758969564065)
      ·
        refine ⟨49245807794587319227173049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65661077059449758969564065 49245807794587319227173049)
        ·
          refine ⟨36934355845940489420379787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49245807794587319227173049 36934355845940489420379787)
          ·
            refine ⟨55401533768910734130569681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36934355845940489420379787 55401533768910734130569681)
            ·
              refine ⟨41551150326683050597927261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55401533768910734130569681 41551150326683050597927261)
              ·
                refine ⟨15581681372506143974222723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41551150326683050597927261 15581681372506143974222723)
                ·
                  refine ⟨23372522058759215961334085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15581681372506143974222723 23372522058759215961334085)
                  ·
                    refine ⟨4382347886017352992750141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23372522058759215961334085 4382347886017352992750141)
                    ·
                      refine ⟨1643380457256507372281303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382347886017352992750141 1643380457256507372281303)
                      ·
                        rfl

theorem cell23_3200472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3200472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200472 prefixEnd_3200472 := by exact prefixLift 3200472
  have htrace : WordTrace (prefixWord ++ tailWord_3200472) baseStart_3200472 baseEnd_3200472 := by
    simpa [prefixWord, tailWord_3200472, baseEnd_3200472] using wordTrace_append hprefix tailTrace_3200472
  have hstable : (prefixWord ++ tailWord_3200472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200472).length < 2 ^ (prefixWord ++ tailWord_3200472).sum := by decide
  have hdescent : baseEnd_3200472 < baseStart_3200472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200496 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 1, 4]
def baseStart_3200496 : Nat := 118140960795 + 3200496 * 2 ^ 59
def prefixEnd_3200496 : Nat := 4983230072969 + 3 ^ 40 * 3200496 * 2
def baseEnd_3200496 : Nat := 547797593597405092793731

theorem tailTrace_3200496 : CollatzResearch.WordTrace tailWord_3200496 prefixEnd_3200496 547797593597405092793731 := by
  unfold tailWord_3200496
  simp only [CollatzResearch.WordTrace]
  refine ⟨58365839506578534022382671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77821119342104712029843561 58365839506578534022382671)
  ·
    refine ⟨87548759259867801033574007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58365839506578534022382671 87548759259867801033574007)
    ·
      refine ⟨131323138889801701550361011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87548759259867801033574007 131323138889801701550361011)
      ·
        refine ⟨196984708334702552325541517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131323138889801701550361011 196984708334702552325541517)
        ·
          refine ⟨73869265625513457122078069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196984708334702552325541517 73869265625513457122078069)
          ·
            refine ⟨6925243652391886605194819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73869265625513457122078069 6925243652391886605194819)
            ·
              refine ⟨10387865478587829907792229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925243652391886605194819 10387865478587829907792229)
              ·
                refine ⟨1947724777235218107711043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10387865478587829907792229 1947724777235218107711043)
                ·
                  refine ⟨2921587165852827161566565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947724777235218107711043 2921587165852827161566565)
                  ·
                    refine ⟨547797593597405092793731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921587165852827161566565 547797593597405092793731)
                    ·
                      rfl

theorem cell23_3200496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 1, 4].length) (baseStart_3200496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200496 prefixEnd_3200496 := by exact prefixLift 3200496
  have htrace : WordTrace (prefixWord ++ tailWord_3200496) baseStart_3200496 baseEnd_3200496 := by
    simpa [prefixWord, tailWord_3200496, baseEnd_3200496] using wordTrace_append hprefix tailTrace_3200496
  have hstable : (prefixWord ++ tailWord_3200496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200496).length < 2 ^ (prefixWord ++ tailWord_3200496).sum := by decide
  have hdescent : baseEnd_3200496 < baseStart_3200496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200523 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 2, 2, 3]
def baseStart_3200523 : Nat := 118140960795 + 3200523 * 2 ^ 59
def prefixEnd_3200523 : Nat := 4983230072969 + 3 ^ 40 * 3200523 * 2
def baseEnd_3200523 : Nat := 1643406644769886672743569

theorem tailTrace_3200523 : CollatzResearch.WordTrace tailWord_3200523 prefixEnd_3200523 1643406644769886672743569 := by
  unfold tailWord_3200523
  simp only [CollatzResearch.WordTrace]
  refine ⟨116732663784059251655998223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77821775856039501103998815 116732663784059251655998223)
  ·
    refine ⟨175098995676088877483997335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116732663784059251655998223 175098995676088877483997335)
    ·
      refine ⟨262648493514133316225996003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175098995676088877483997335 262648493514133316225996003)
      ·
        refine ⟨393972740271199974338994005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262648493514133316225996003 393972740271199974338994005)
        ·
          refine ⟨2308434025026562349642543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 393972740271199974338994005 2308434025026562349642543)
          ·
            refine ⟨3462651037539843524463815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308434025026562349642543 3462651037539843524463815)
            ·
              refine ⟨5193976556309765286695723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462651037539843524463815 5193976556309765286695723)
              ·
                refine ⟨7790964834464647930043585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193976556309765286695723 7790964834464647930043585)
                ·
                  refine ⟨5843223625848485947532689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7790964834464647930043585 5843223625848485947532689)
                  ·
                    refine ⟨4382417719386364460649517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843223625848485947532689 4382417719386364460649517)
                    ·
                      refine ⟨1643406644769886672743569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382417719386364460649517 1643406644769886672743569)
                      ·
                        rfl

theorem cell23_3200523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 2, 2, 3].length) (baseStart_3200523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200523 prefixEnd_3200523 := by exact prefixLift 3200523
  have htrace : WordTrace (prefixWord ++ tailWord_3200523) baseStart_3200523 baseEnd_3200523 := by
    simpa [prefixWord, tailWord_3200523, baseEnd_3200523] using wordTrace_append hprefix tailTrace_3200523
  have hstable : (prefixWord ++ tailWord_3200523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200523).length < 2 ^ (prefixWord ++ tailWord_3200523).sum := by decide
  have hdescent : baseEnd_3200523 < baseStart_3200523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200529 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_3200529 : Nat := 118140960795 + 3200529 * 2 ^ 59
def prefixEnd_3200529 : Nat := 4983230072969 + 3 ^ 40 * 3200529 * 2
def baseEnd_3200529 : Nat := 1643409725653813649268541

theorem tailTrace_3200529 : CollatzResearch.WordTrace tailWord_3200529 prefixEnd_3200529 1643409725653813649268541 := by
  unfold tailWord_3200529
  simp only [CollatzResearch.WordTrace]
  refine ⟨116732882622037514680716641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77821921748025009787144427 116732882622037514680716641)
  ·
    refine ⟨87549661966528136010537481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116732882622037514680716641 87549661966528136010537481)
    ·
      refine ⟨65662246474896102007903111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87549661966528136010537481 65662246474896102007903111)
      ·
        refine ⟨98493369712344153011854667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65662246474896102007903111 98493369712344153011854667)
        ·
          refine ⟨147740054568516229517782001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98493369712344153011854667 147740054568516229517782001)
          ·
            refine ⟨110805040926387172138336501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147740054568516229517782001 110805040926387172138336501)
            ·
              refine ⟨10387972586848797387969047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110805040926387172138336501 10387972586848797387969047)
              ·
                refine ⟨15581958880273196081953571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387972586848797387969047 15581958880273196081953571)
                ·
                  refine ⟨23372938320409794122930357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15581958880273196081953571 23372938320409794122930357)
                  ·
                    refine ⟨2191212967538418199024721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23372938320409794122930357 2191212967538418199024721)
                    ·
                      refine ⟨1643409725653813649268541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191212967538418199024721 1643409725653813649268541)
                      ·
                        rfl

theorem cell23_3200529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_3200529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200529 prefixEnd_3200529 := by exact prefixLift 3200529
  have htrace : WordTrace (prefixWord ++ tailWord_3200529) baseStart_3200529 baseEnd_3200529 := by
    simpa [prefixWord, tailWord_3200529, baseEnd_3200529] using wordTrace_append hprefix tailTrace_3200529
  have hstable : (prefixWord ++ tailWord_3200529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200529).length < 2 ^ (prefixWord ++ tailWord_3200529).sum := by decide
  have hdescent : baseEnd_3200529 < baseStart_3200529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200546 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_3200546 : Nat := 118140960795 + 3200546 * 2 ^ 59
def prefixEnd_3200546 : Nat := 4983230072969 + 3 ^ 40 * 3200546 * 2
def baseEnd_3200546 : Nat := 1643418454824940082755963

theorem tailTrace_3200546 : CollatzResearch.WordTrace tailWord_3200546 prefixEnd_3200546 1643418454824940082755963 := by
  unfold tailWord_3200546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183375665743981646021373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77822335108650617722723661 29183375665743981646021373)
  ·
    refine ⟨10943765874653993117258015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29183375665743981646021373 10943765874653993117258015)
    ·
      refine ⟨16415648811980989675887023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10943765874653993117258015 16415648811980989675887023)
      ·
        refine ⟨24623473217971484513830535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16415648811980989675887023 24623473217971484513830535)
        ·
          refine ⟨36935209826957226770745803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24623473217971484513830535 36935209826957226770745803)
          ·
            refine ⟨55402814740435840156118705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36935209826957226770745803 55402814740435840156118705)
            ·
              refine ⟨41552111055326880117089029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55402814740435840156118705 41552111055326880117089029)
              ·
                refine ⟨7791020822873790021954193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41552111055326880117089029 7791020822873790021954193)
                ·
                  refine ⟨5843265617155342516465645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791020822873790021954193 5843265617155342516465645)
                  ·
                    refine ⟨2191224606433253443674617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5843265617155342516465645 2191224606433253443674617)
                    ·
                      refine ⟨1643418454824940082755963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191224606433253443674617 1643418454824940082755963)
                      ·
                        rfl

theorem cell23_3200546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_3200546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200546 prefixEnd_3200546 := by exact prefixLift 3200546
  have htrace : WordTrace (prefixWord ++ tailWord_3200546) baseStart_3200546 baseEnd_3200546 := by
    simpa [prefixWord, tailWord_3200546, baseEnd_3200546] using wordTrace_append hprefix tailTrace_3200546
  have hstable : (prefixWord ++ tailWord_3200546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200546).length < 2 ^ (prefixWord ++ tailWord_3200546).sum := by decide
  have hdescent : baseEnd_3200546 < baseStart_3200546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200569 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_3200569 : Nat := 118140960795 + 3200569 * 2 ^ 59
def prefixEnd_3200569 : Nat := 4983230072969 + 3 ^ 40 * 3200569 * 2
def baseEnd_3200569 : Nat := 547810088293331164256119

theorem tailTrace_3200569 : CollatzResearch.WordTrace tailWord_3200569 prefixEnd_3200569 547810088293331164256119 := by
  unfold tailWord_3200569
  simp only [CollatzResearch.WordTrace]
  refine ⟨116734341541892601512172761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77822894361261734341448507 116734341541892601512172761)
  ·
    refine ⟨87550756156419451134129571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116734341541892601512172761 87550756156419451134129571)
    ·
      refine ⟨131326134234629176701194357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87550756156419451134129571 131326134234629176701194357)
      ·
        refine ⟨12311825084496485315736971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131326134234629176701194357 12311825084496485315736971)
        ·
          refine ⟨18467737626744727973605457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311825084496485315736971 18467737626744727973605457)
          ·
            refine ⟨13850803220058545980204093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18467737626744727973605457 13850803220058545980204093)
            ·
              refine ⟨5194051207521954742576535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13850803220058545980204093 5194051207521954742576535)
              ·
                refine ⟨7791076811282932113864803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194051207521954742576535 7791076811282932113864803)
                ·
                  refine ⟨11686615216924398170797205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791076811282932113864803 11686615216924398170797205)
                  ·
                    refine ⟨547810088293331164256119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11686615216924398170797205 547810088293331164256119)
                    ·
                      rfl

theorem cell23_3200569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_3200569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200569 prefixEnd_3200569 := by exact prefixLift 3200569
  have htrace : WordTrace (prefixWord ++ tailWord_3200569) baseStart_3200569 baseEnd_3200569 := by
    simpa [prefixWord, tailWord_3200569, baseEnd_3200569] using wordTrace_append hprefix tailTrace_3200569
  have hstable : (prefixWord ++ tailWord_3200569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200569).length < 2 ^ (prefixWord ++ tailWord_3200569).sum := by decide
  have hdescent : baseEnd_3200569 < baseStart_3200569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200596 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3200596 : Nat := 118140960795 + 3200596 * 2 ^ 59
def prefixEnd_3200596 : Nat := 4983230072969 + 3 ^ 40 * 3200596 * 2
def baseEnd_3200596 : Nat := 1643444128857664887130733

theorem tailTrace_3200596 : CollatzResearch.WordTrace tailWord_3200596 prefixEnd_3200596 1643444128857664887130733 := by
  unfold tailWord_3200596
  simp only [CollatzResearch.WordTrace]
  refine ⟨58367663156397392561702821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77823550875196523415603761 58367663156397392561702821)
  ·
    refine ⟨10943936841824511105319279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58367663156397392561702821 10943936841824511105319279)
    ·
      refine ⟨16415905262736766657978919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10943936841824511105319279 16415905262736766657978919)
      ·
        refine ⟨24623857894105149986968379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16415905262736766657978919 24623857894105149986968379)
        ·
          refine ⟨36935786841157724980452569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24623857894105149986968379 36935786841157724980452569)
          ·
            refine ⟨27701840130868293735339427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36935786841157724980452569 27701840130868293735339427)
            ·
              refine ⟨41552760196302440603009141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27701840130868293735339427 41552760196302440603009141)
              ·
                refine ⟨3895571268403353806532107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41552760196302440603009141 3895571268403353806532107)
                ·
                  refine ⟨5843356902605030709798161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895571268403353806532107 5843356902605030709798161)
                  ·
                    refine ⟨4382517676953773032348621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843356902605030709798161 4382517676953773032348621)
                    ·
                      refine ⟨1643444128857664887130733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382517676953773032348621 1643444128857664887130733)
                      ·
                        rfl

theorem cell23_3200596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3200596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200596 prefixEnd_3200596 := by exact prefixLift 3200596
  have htrace : WordTrace (prefixWord ++ tailWord_3200596) baseStart_3200596 baseEnd_3200596 := by
    simpa [prefixWord, tailWord_3200596, baseEnd_3200596] using wordTrace_append hprefix tailTrace_3200596
  have hstable : (prefixWord ++ tailWord_3200596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200596).length < 2 ^ (prefixWord ++ tailWord_3200596).sum := by decide
  have hdescent : baseEnd_3200596 < baseStart_3200596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200630 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3200630 : Nat := 118140960795 + 3200630 * 2 ^ 59
def prefixEnd_3200630 : Nat := 4983230072969 + 3 ^ 40 * 3200630 * 2
def baseEnd_3200630 : Nat := 1643461587199917754105577

theorem tailTrace_3200630 : CollatzResearch.WordTrace tailWord_3200630 prefixEnd_3200630 1643461587199917754105577 := by
  unfold tailWord_3200630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296035399666975558133959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77824377596447739286762229 7296035399666975558133959)
  ·
    refine ⟨10944053099500463337200939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296035399666975558133959 10944053099500463337200939)
    ·
      refine ⟨16416079649250695005801409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10944053099500463337200939 16416079649250695005801409)
      ·
        refine ⟨12312059736938021254351057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16416079649250695005801409 12312059736938021254351057)
        ·
          refine ⟨9234044802703515940763293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12312059736938021254351057 9234044802703515940763293)
          ·
            refine ⟨3462766801013818477786235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9234044802703515940763293 3462766801013818477786235)
            ·
              refine ⟨5194150201520727716679353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462766801013818477786235 5194150201520727716679353)
              ·
                refine ⟨3895612651140545787509515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194150201520727716679353 3895612651140545787509515)
                ·
                  refine ⟨5843418976710818681264273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895612651140545787509515 5843418976710818681264273)
                  ·
                    refine ⟨4382564232533114010948205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5843418976710818681264273 4382564232533114010948205)
                    ·
                      refine ⟨1643461587199917754105577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382564232533114010948205 1643461587199917754105577)
                      ·
                        rfl

theorem cell23_3200630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3200630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200630 prefixEnd_3200630 := by exact prefixLift 3200630
  have htrace : WordTrace (prefixWord ++ tailWord_3200630) baseStart_3200630 baseEnd_3200630 := by
    simpa [prefixWord, tailWord_3200630, baseEnd_3200630] using wordTrace_append hprefix tailTrace_3200630
  have hstable : (prefixWord ++ tailWord_3200630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200630).length < 2 ^ (prefixWord ++ tailWord_3200630).sum := by decide
  have hdescent : baseEnd_3200630 < baseStart_3200630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200717 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3200717 : Nat := 118140960795 + 3200717 * 2 ^ 59
def prefixEnd_3200717 : Nat := 4983230072969 + 3 ^ 40 * 3200717 * 2
def baseEnd_3200717 : Nat := 1643506260016858913717677

theorem tailTrace_3200717 : CollatzResearch.WordTrace tailWord_3200717 prefixEnd_3200717 1643506260016858913717677 := by
  unfold tailWord_3200717
  simp only [CollatzResearch.WordTrace]
  refine ⟨116739739545356422788560405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77826493030237615192373603 116739739545356422788560405)
  ·
    refine ⟨5472175291188582318213769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116739739545356422788560405 5472175291188582318213769)
    ·
      refine ⟨4104131468391436738660327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472175291188582318213769 4104131468391436738660327)
      ·
        refine ⟨6156197202587155107990491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104131468391436738660327 6156197202587155107990491)
        ·
          refine ⟨9234295803880732661985737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6156197202587155107990491 9234295803880732661985737)
          ·
            refine ⟨6925721852910549496489303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9234295803880732661985737 6925721852910549496489303)
            ·
              refine ⟨10388582779365824244733955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925721852910549496489303 10388582779365824244733955)
              ·
                refine ⟨15582874169048736367100933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388582779365824244733955 15582874169048736367100933)
                ·
                  refine ⟨2921788906696638068831425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15582874169048736367100933 2921788906696638068831425)
                  ·
                    refine ⟨2191341680022478551623569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2921788906696638068831425 2191341680022478551623569)
                    ·
                      refine ⟨1643506260016858913717677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191341680022478551623569 1643506260016858913717677)
                      ·
                        rfl

theorem cell23_3200717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3200717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200717 prefixEnd_3200717 := by exact prefixLift 3200717
  have htrace : WordTrace (prefixWord ++ tailWord_3200717) baseStart_3200717 baseEnd_3200717 := by
    simpa [prefixWord, tailWord_3200717, baseEnd_3200717] using wordTrace_append hprefix tailTrace_3200717
  have hstable : (prefixWord ++ tailWord_3200717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200717).length < 2 ^ (prefixWord ++ tailWord_3200717).sum := by decide
  have hdescent : baseEnd_3200717 < baseStart_3200717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200719 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 2, 5]
def baseStart_3200719 : Nat := 118140960795 + 3200719 * 2 ^ 59
def prefixEnd_3200719 : Nat := 4983230072969 + 3 ^ 40 * 3200719 * 2
def baseEnd_3200719 : Nat := 547835762326055968630889

theorem tailTrace_3200719 : CollatzResearch.WordTrace tailWord_3200719 prefixEnd_3200719 547835762326055968630889 := by
  unfold tailWord_3200719
  simp only [CollatzResearch.WordTrace]
  refine ⟨116739812491349177130133211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77826541660899451420088807 116739812491349177130133211)
  ·
    refine ⟨175109718737023765695199817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116739812491349177130133211 175109718737023765695199817)
    ·
      refine ⟨131332289052767824271399863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175109718737023765695199817 131332289052767824271399863)
      ·
        refine ⟨196998433579151736407099795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131332289052767824271399863 196998433579151736407099795)
        ·
          refine ⟨295497650368727604610649693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196998433579151736407099795 295497650368727604610649693)
          ·
            refine ⟨110811618888272851728993635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295497650368727604610649693 110811618888272851728993635)
            ·
              refine ⟨166217428332409277593490453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110811618888272851728993635 166217428332409277593490453)
              ·
                refine ⟨7791441953081684887194865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166217428332409277593490453 7791441953081684887194865)
                ·
                  refine ⟨5843581464811263665396149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791441953081684887194865 5843581464811263665396149)
                  ·
                    refine ⟨547835762326055968630889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5843581464811263665396149 547835762326055968630889)
                    ·
                      rfl

theorem cell23_3200719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_3200719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200719 prefixEnd_3200719 := by exact prefixLift 3200719
  have htrace : WordTrace (prefixWord ++ tailWord_3200719) baseStart_3200719 baseEnd_3200719 := by
    simpa [prefixWord, tailWord_3200719, baseEnd_3200719] using wordTrace_append hprefix tailTrace_3200719
  have hstable : (prefixWord ++ tailWord_3200719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200719).length < 2 ^ (prefixWord ++ tailWord_3200719).sum := by decide
  have hdescent : baseEnd_3200719 < baseStart_3200719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200769 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3200769 : Nat := 118140960795 + 3200769 * 2 ^ 59
def prefixEnd_3200769 : Nat := 4983230072969 + 3 ^ 40 * 3200769 * 2
def baseEnd_3200769 : Nat := 1643532961010892710267437

theorem tailTrace_3200769 : CollatzResearch.WordTrace tailWord_3200769 prefixEnd_3200769 1643532961010892710267437 := by
  unfold tailWord_3200769
  simp only [CollatzResearch.WordTrace]
  refine ⟨116741636141168035669453361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77827757427445357112968907 116741636141168035669453361)
  ·
    refine ⟨87556227105876026752090021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116741636141168035669453361 87556227105876026752090021)
    ·
      refine ⟨16416792582351755016016879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87556227105876026752090021 16416792582351755016016879)
      ·
        refine ⟨24625188873527632524025319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16416792582351755016016879 24625188873527632524025319)
        ·
          refine ⟨36937783310291448786037979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24625188873527632524025319 36937783310291448786037979)
          ·
            refine ⟨55406674965437173179056969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36937783310291448786037979 55406674965437173179056969)
            ·
              refine ⟨41555006224077879884292727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55406674965437173179056969 41555006224077879884292727)
              ·
                refine ⟨62332509336116819826439091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41555006224077879884292727 62332509336116819826439091)
                ·
                  refine ⟨93498764004175229739658637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62332509336116819826439091 93498764004175229739658637)
                  ·
                    refine ⟨35062036501565711152371989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93498764004175229739658637 35062036501565711152371989)
                    ·
                      refine ⟨1643532961010892710267437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35062036501565711152371989 1643532961010892710267437)
                      ·
                        rfl

theorem cell23_3200769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3200769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200769 prefixEnd_3200769 := by exact prefixLift 3200769
  have htrace : WordTrace (prefixWord ++ tailWord_3200769) baseStart_3200769 baseEnd_3200769 := by
    simpa [prefixWord, tailWord_3200769, baseEnd_3200769] using wordTrace_append hprefix tailTrace_3200769
  have hstable : (prefixWord ++ tailWord_3200769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200769).length < 2 ^ (prefixWord ++ tailWord_3200769).sum := by decide
  have hdescent : baseEnd_3200769 < baseStart_3200769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200779 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 8]
def baseStart_3200779 : Nat := 118140960795 + 3200779 * 2 ^ 59
def prefixEnd_3200779 : Nat := 4983230072969 + 3 ^ 40 * 3200779 * 2
def baseEnd_3200779 : Nat := 182615343979715296793599

theorem tailTrace_3200779 : CollatzResearch.WordTrace tailWord_3200779 prefixEnd_3200779 182615343979715296793599 := by
  unfold tailWord_3200779
  simp only [CollatzResearch.WordTrace]
  refine ⟨116742000871131807377317391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77828000580754538251544927 116742000871131807377317391)
  ·
    refine ⟨175113001306697711065976087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116742000871131807377317391 175113001306697711065976087)
    ·
      refine ⟨262669501960046566598964131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175113001306697711065976087 262669501960046566598964131)
      ·
        refine ⟨394004252940069849898446197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262669501960046566598964131 394004252940069849898446197)
        ·
          refine ⟨36937898713131548427979331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394004252940069849898446197 36937898713131548427979331)
          ·
            refine ⟨55406848069697322641968997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36937898713131548427979331 55406848069697322641968997)
            ·
              refine ⟨10388784013068247995369187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55406848069697322641968997 10388784013068247995369187)
              ·
                refine ⟨15583176019602371993053781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388784013068247995369187 15583176019602371993053781)
                ·
                  refine ⟨182615343979715296793599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15583176019602371993053781 182615343979715296793599)
                  ·
                    rfl

theorem cell23_3200779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 8].length) (baseStart_3200779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200779 prefixEnd_3200779 := by exact prefixLift 3200779
  have htrace : WordTrace (prefixWord ++ tailWord_3200779) baseStart_3200779 baseEnd_3200779 := by
    simpa [prefixWord, tailWord_3200779, baseEnd_3200779] using wordTrace_append hprefix tailTrace_3200779
  have hstable : (prefixWord ++ tailWord_3200779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200779).length < 2 ^ (prefixWord ++ tailWord_3200779).sum := by decide
  have hdescent : baseEnd_3200779 < baseStart_3200779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200796 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 6]
def baseStart_3200796 : Nat := 118140960795 + 3200796 * 2 ^ 59
def prefixEnd_3200796 : Nat := 4983230072969 + 3 ^ 40 * 3200796 * 2
def baseEnd_3200796 : Nat := 182616313887618233847757

theorem tailTrace_3200796 : CollatzResearch.WordTrace tailWord_3200796 prefixEnd_3200796 182616313887618233847757 := by
  unfold tailWord_3200796
  simp only [CollatzResearch.WordTrace]
  refine ⟨58371310456035109640343121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77828413941380146187124161 58371310456035109640343121)
  ·
    refine ⟨43778482842026332230257341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58371310456035109640343121 43778482842026332230257341)
    ·
      refine ⟨16416931065759874586346503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43778482842026332230257341 16416931065759874586346503)
      ·
        refine ⟨24625396598639811879519755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16416931065759874586346503 24625396598639811879519755)
        ·
          refine ⟨36938094897959717819279633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24625396598639811879519755 36938094897959717819279633)
          ·
            refine ⟨27703571173469788364459725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36938094897959717819279633 27703571173469788364459725)
            ·
              refine ⟨10388839190051170636672397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27703571173469788364459725 10388839190051170636672397)
              ·
                refine ⟨3895814696269188988752149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10388839190051170636672397 3895814696269188988752149)
                ·
                  refine ⟨182616313887618233847757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3895814696269188988752149 182616313887618233847757)
                  ·
                    rfl

theorem cell23_3200796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_3200796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200796 prefixEnd_3200796 := by exact prefixLift 3200796
  have htrace : WordTrace (prefixWord ++ tailWord_3200796) baseStart_3200796 baseEnd_3200796 := by
    simpa [prefixWord, tailWord_3200796, baseEnd_3200796] using wordTrace_append hprefix tailTrace_3200796
  have hstable : (prefixWord ++ tailWord_3200796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200796).length < 2 ^ (prefixWord ++ tailWord_3200796).sum := by decide
  have hdescent : baseEnd_3200796 < baseStart_3200796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200856 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_3200856 : Nat := 118140960795 + 3200856 * 2 ^ 59
def prefixEnd_3200856 : Nat := 4983230072969 + 3 ^ 40 * 3200856 * 2
def baseEnd_3200856 : Nat := 547859211275944623293179

theorem tailTrace_3200856 : CollatzResearch.WordTrace tailWord_3200856 prefixEnd_3200856 547859211275944623293179 := by
  unfold tailWord_3200856
  simp only [CollatzResearch.WordTrace]
  refine ⟨58372404645926424763935211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77829872861235233018580281 58372404645926424763935211)
  ·
    refine ⟨87558606968889637145902817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58372404645926424763935211 87558606968889637145902817)
    ·
      refine ⟨65668955226667227859427113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87558606968889637145902817 65668955226667227859427113)
      ·
        refine ⟨49251716420000420894570335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65668955226667227859427113 49251716420000420894570335)
        ·
          refine ⟨73877574630000631341855503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49251716420000420894570335 73877574630000631341855503)
          ·
            refine ⟨110816361945000947012783255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73877574630000631341855503 110816361945000947012783255)
            ·
              refine ⟨166224542917501420519174883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110816361945000947012783255 166224542917501420519174883)
              ·
                refine ⟨249336814376252130778762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166224542917501420519174883 249336814376252130778762325)
                ·
                  refine ⟨2921915793471704657563621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 249336814376252130778762325 2921915793471704657563621)
                  ·
                    refine ⟨547859211275944623293179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921915793471704657563621 547859211275944623293179)
                    ·
                      rfl

theorem cell23_3200856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_3200856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200856 prefixEnd_3200856 := by exact prefixLift 3200856
  have htrace : WordTrace (prefixWord ++ tailWord_3200856) baseStart_3200856 baseEnd_3200856 := by
    simpa [prefixWord, tailWord_3200856, baseEnd_3200856] using wordTrace_append hprefix tailTrace_3200856
  have hstable : (prefixWord ++ tailWord_3200856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200856).length < 2 ^ (prefixWord ++ tailWord_3200856).sum := by decide
  have hdescent : baseEnd_3200856 < baseStart_3200856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200867 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 2, 3, 2]
def baseStart_3200867 : Nat := 118140960795 + 3200867 * 2 ^ 59
def prefixEnd_3200867 : Nat := 4983230072969 + 3 ^ 40 * 3200867 * 2
def baseEnd_3200867 : Nat := 1643583282115033326841987

theorem tailTrace_3200867 : CollatzResearch.WordTrace tailWord_3200867 prefixEnd_3200867 1643583282115033326841987 := by
  unfold tailWord_3200867
  simp only [CollatzResearch.WordTrace]
  refine ⟨116745210494812998406520855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77830140329875332271013903 116745210494812998406520855)
  ·
    refine ⟨175117815742219497609781283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116745210494812998406520855 175117815742219497609781283)
    ·
      refine ⟨262676723613329246414671925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175117815742219497609781283 262676723613329246414671925)
      ·
        refine ⟨24625942838749616851375493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262676723613329246414671925 24625942838749616851375493)
        ·
          refine ⟨4617364282265553159632905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24625942838749616851375493 4617364282265553159632905)
          ·
            refine ⟨3463023211699164869724679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617364282265553159632905 3463023211699164869724679)
            ·
              refine ⟨5194534817548747304587019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463023211699164869724679 5194534817548747304587019)
              ·
                refine ⟨7791802226323120956880529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194534817548747304587019 7791802226323120956880529)
                ·
                  refine ⟨5843851669742340717660397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791802226323120956880529 5843851669742340717660397)
                  ·
                    refine ⟨2191444376153377769122649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5843851669742340717660397 2191444376153377769122649)
                    ·
                      refine ⟨1643583282115033326841987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191444376153377769122649 1643583282115033326841987)
                      ·
                        rfl

theorem cell23_3200867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_3200867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200867 prefixEnd_3200867 := by exact prefixLift 3200867
  have htrace : WordTrace (prefixWord ++ tailWord_3200867) baseStart_3200867 baseEnd_3200867 := by
    simpa [prefixWord, tailWord_3200867, baseEnd_3200867] using wordTrace_append hprefix tailTrace_3200867
  have hstable : (prefixWord ++ tailWord_3200867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200867).length < 2 ^ (prefixWord ++ tailWord_3200867).sum := by decide
  have hdescent : baseEnd_3200867 < baseStart_3200867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200910 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3200910 : Nat := 118140960795 + 3200910 * 2 ^ 59
def prefixEnd_3200910 : Nat := 4983230072969 + 3 ^ 40 * 3200910 * 2
def baseEnd_3200910 : Nat := 1643605361783176658604289

theorem tailTrace_3200910 : CollatzResearch.WordTrace tailWord_3200910 prefixEnd_3200910 1643605361783176658604289 := by
  unfold tailWord_3200910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14593347354207152093792023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77831185889104811166890789 14593347354207152093792023)
  ·
    refine ⟨21890021031310728140688035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14593347354207152093792023 21890021031310728140688035)
    ·
      refine ⟨32835031546966092211032053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21890021031310728140688035 32835031546966092211032053)
      ·
        refine ⟨3078284207528071144784255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32835031546966092211032053 3078284207528071144784255)
        ·
          refine ⟨4617426311292106717176383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078284207528071144784255 4617426311292106717176383)
          ·
            refine ⟨6926139466938160075764575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617426311292106717176383 6926139466938160075764575)
            ·
              refine ⟨10389209200407240113646863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926139466938160075764575 10389209200407240113646863)
              ·
                refine ⟨15583813800610860170470295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10389209200407240113646863 15583813800610860170470295)
                ·
                  refine ⟨23375720700916290255705443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15583813800610860170470295 23375720700916290255705443)
                  ·
                    refine ⟨35063581051374435383558165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23375720700916290255705443 35063581051374435383558165)
                    ·
                      refine ⟨1643605361783176658604289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35063581051374435383558165 1643605361783176658604289)
                      ·
                        rfl

theorem cell23_3200910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3200910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200910 prefixEnd_3200910 := by exact prefixLift 3200910
  have htrace : WordTrace (prefixWord ++ tailWord_3200910) baseStart_3200910 baseEnd_3200910 := by
    simpa [prefixWord, tailWord_3200910, baseEnd_3200910] using wordTrace_append hprefix tailTrace_3200910
  have hstable : (prefixWord ++ tailWord_3200910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200910).length < 2 ^ (prefixWord ++ tailWord_3200910).sum := by decide
  have hdescent : baseEnd_3200910 < baseStart_3200910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200913 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_3200913 : Nat := 118140960795 + 3200913 * 2 ^ 59
def prefixEnd_3200913 : Nat := 4983230072969 + 3 ^ 40 * 3200913 * 2
def baseEnd_3200913 : Nat := 1643606902225140146866775

theorem tailTrace_3200913 : CollatzResearch.WordTrace tailWord_3200913 prefixEnd_3200913 1643606902225140146866775 := by
  unfold tailWord_3200913
  simp only [CollatzResearch.WordTrace]
  refine ⟨116746888252646348262695393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77831258835097565508463595 116746888252646348262695393)
  ·
    refine ⟨87560166189484761197021545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116746888252646348262695393 87560166189484761197021545)
    ·
      refine ⟨65670124642113570897766159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87560166189484761197021545 65670124642113570897766159)
      ·
        refine ⟨98505186963170356346649239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65670124642113570897766159 98505186963170356346649239)
        ·
          refine ⟨147757780444755534519973859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98505186963170356346649239 147757780444755534519973859)
          ·
            refine ⟨221636670667133301779960789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147757780444755534519973859 221636670667133301779960789)
            ·
              refine ⟨5194609468760936760467831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221636670667133301779960789 5194609468760936760467831)
              ·
                refine ⟨7791914203141405140701747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194609468760936760467831 7791914203141405140701747)
                ·
                  refine ⟨11687871304712107711052621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791914203141405140701747 11687871304712107711052621)
                  ·
                    refine ⟨4382951739267040391644733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11687871304712107711052621 4382951739267040391644733)
                    ·
                      refine ⟨1643606902225140146866775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4382951739267040391644733 1643606902225140146866775)
                      ·
                        rfl

theorem cell23_3200913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_3200913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200913 prefixEnd_3200913 := by exact prefixLift 3200913
  have htrace : WordTrace (prefixWord ++ tailWord_3200913) baseStart_3200913 baseEnd_3200913 := by
    simpa [prefixWord, tailWord_3200913, baseEnd_3200913] using wordTrace_append hprefix tailTrace_3200913
  have hstable : (prefixWord ++ tailWord_3200913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200913).length < 2 ^ (prefixWord ++ tailWord_3200913).sum := by decide
  have hdescent : baseEnd_3200913 < baseStart_3200913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200946 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_3200946 : Nat := 118140960795 + 3200946 * 2 ^ 59
def prefixEnd_3200946 : Nat := 4983230072969 + 3 ^ 40 * 3200946 * 2
def baseEnd_3200946 : Nat := 547874615695579505918041

theorem tailTrace_3200946 : CollatzResearch.WordTrace tailWord_3200946 prefixEnd_3200946 547874615695579505918041 := by
  unfold tailWord_3200946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29187022965381698724661673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77832061241017863265764461 29187022965381698724661673)
  ·
    refine ⟨21890267224036274043496255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29187022965381698724661673 21890267224036274043496255)
    ·
      refine ⟨32835400836054411065244383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21890267224036274043496255 32835400836054411065244383)
      ·
        refine ⟨49253101254081616597866575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32835400836054411065244383 49253101254081616597866575)
        ·
          refine ⟨73879651881122424896799863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49253101254081616597866575 73879651881122424896799863)
          ·
            refine ⟨110819477821683637345199795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73879651881122424896799863 110819477821683637345199795)
            ·
              refine ⟨166229216732525456017799693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110819477821683637345199795 166229216732525456017799693)
              ·
                refine ⟨62335956274697046006674885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166229216732525456017799693 62335956274697046006674885)
                ·
                  refine ⟨11687991801505696126251541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62335956274697046006674885 11687991801505696126251541)
                  ·
                    refine ⟨547874615695579505918041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11687991801505696126251541 547874615695579505918041)
                    ·
                      rfl

theorem cell23_3200946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_3200946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200946 prefixEnd_3200946 := by exact prefixLift 3200946
  have htrace : WordTrace (prefixWord ++ tailWord_3200946) baseStart_3200946 baseEnd_3200946 := by
    simpa [prefixWord, tailWord_3200946, baseEnd_3200946] using wordTrace_append hprefix tailTrace_3200946
  have hstable : (prefixWord ++ tailWord_3200946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200946).length < 2 ^ (prefixWord ++ tailWord_3200946).sum := by decide
  have hdescent : baseEnd_3200946 < baseStart_3200946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200948 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3200948 : Nat := 118140960795 + 3200948 * 2 ^ 59
def prefixEnd_3200948 : Nat := 4983230072969 + 3 ^ 40 * 3200948 * 2
def baseEnd_3200948 : Nat := 1643624874048047509929115

theorem tailTrace_3200948 : CollatzResearch.WordTrace tailWord_3200948 prefixEnd_3200948 1643624874048047509929115 := by
  unfold tailWord_3200948
  simp only [CollatzResearch.WordTrace]
  refine ⟨58374082403759774620109749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77832109871679699493479665 58374082403759774620109749)
  ·
    refine ⟨5472570225352478870635289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58374082403759774620109749 5472570225352478870635289)
    ·
      refine ⟨4104427669014359152976467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472570225352478870635289 4104427669014359152976467)
      ·
        refine ⟨6156641503521538729464701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104427669014359152976467 6156641503521538729464701)
        ·
          refine ⟨2308740563820577023549263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6156641503521538729464701 2308740563820577023549263)
          ·
            refine ⟨3463110845730865535323895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308740563820577023549263 3463110845730865535323895)
            ·
              refine ⟨5194666268596298302985843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463110845730865535323895 5194666268596298302985843)
              ·
                refine ⟨7791999402894447454478765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194666268596298302985843 7791999402894447454478765)
                ·
                  refine ⟨2921999776085417795429537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7791999402894447454478765 2921999776085417795429537)
                  ·
                    refine ⟨2191499832064063346572153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2921999776085417795429537 2191499832064063346572153)
                    ·
                      refine ⟨1643624874048047509929115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191499832064063346572153 1643624874048047509929115)
                      ·
                        rfl

theorem cell23_3200948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3200948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200948 prefixEnd_3200948 := by exact prefixLift 3200948
  have htrace : WordTrace (prefixWord ++ tailWord_3200948) baseStart_3200948 baseEnd_3200948 := by
    simpa [prefixWord, tailWord_3200948, baseEnd_3200948] using wordTrace_append hprefix tailTrace_3200948
  have hstable : (prefixWord ++ tailWord_3200948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200948).length < 2 ^ (prefixWord ++ tailWord_3200948).sum := by decide
  have hdescent : baseEnd_3200948 < baseStart_3200948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200976 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 7]
def baseStart_3200976 : Nat := 118140960795 + 3200976 * 2 ^ 59
def prefixEnd_3200976 : Nat := 4983230072969 + 3 ^ 40 * 3200976 * 2
def baseEnd_3200976 : Nat := 182626583500708155597665

theorem tailTrace_3200976 : CollatzResearch.WordTrace tailWord_3200976 prefixEnd_3200976 182626583500708155597665 := by
  unfold tailWord_3200976
  simp only [CollatzResearch.WordTrace]
  refine ⟨58374593025709055011119391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77832790700945406681492521 58374593025709055011119391)
  ·
    refine ⟨87561889538563582516679087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58374593025709055011119391 87561889538563582516679087)
    ·
      refine ⟨131342834307845373775018631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87561889538563582516679087 131342834307845373775018631)
      ·
        refine ⟨197014251461768060662527947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131342834307845373775018631 197014251461768060662527947)
        ·
          refine ⟨295521377192652090993791921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197014251461768060662527947 295521377192652090993791921)
          ·
            refine ⟨221641032894489068245343941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295521377192652090993791921 221641032894489068245343941)
            ·
              refine ⟨41557693667716700296001989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221641032894489068245343941 41557693667716700296001989)
              ·
                refine ⟨7792067562696881305500373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41557693667716700296001989 7792067562696881305500373)
                ·
                  refine ⟨182626583500708155597665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7792067562696881305500373 182626583500708155597665)
                  ·
                    rfl

theorem cell23_3200976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_3200976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3200976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3200976 prefixEnd_3200976 := by exact prefixLift 3200976
  have htrace : WordTrace (prefixWord ++ tailWord_3200976) baseStart_3200976 baseEnd_3200976 := by
    simpa [prefixWord, tailWord_3200976, baseEnd_3200976] using wordTrace_append hprefix tailTrace_3200976
  have hstable : (prefixWord ++ tailWord_3200976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200976).length < 2 ^ (prefixWord ++ tailWord_3200976).sum := by decide
  have hdescent : baseEnd_3200976 < baseStart_3200976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201093 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_3201093 : Nat := 118140960795 + 3201093 * 2 ^ 59
def prefixEnd_3201093 : Nat := 4983230072969 + 3 ^ 40 * 3201093 * 2
def baseEnd_3201093 : Nat := 1643699328742949442615947

theorem tailTrace_3201093 : CollatzResearch.WordTrace tailWord_3201093 prefixEnd_3201093 1643699328742949442615947 := by
  unfold tailWord_3201093
  simp only [CollatzResearch.WordTrace]
  refine ⟨116753453391994239004247933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77835635594662826002831955 116753453391994239004247933)
  ·
    refine ⟨43782545021997839626592975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116753453391994239004247933 43782545021997839626592975)
    ·
      refine ⟨65673817532996759439889463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43782545021997839626592975 65673817532996759439889463)
      ·
        refine ⟨98510726299495139159834195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65673817532996759439889463 98510726299495139159834195)
        ·
          refine ⟨147766089449242708739751293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98510726299495139159834195 147766089449242708739751293)
          ·
            refine ⟨55412283543466015777406735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147766089449242708739751293 55412283543466015777406735)
            ·
              refine ⟨83118425315199023666110103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55412283543466015777406735 83118425315199023666110103)
              ·
                refine ⟨124677637972798535499165155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83118425315199023666110103 124677637972798535499165155)
                ·
                  refine ⟨187016456959197803248747733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124677637972798535499165155 187016456959197803248747733)
                  ·
                    refine ⟨4383198209981198513642525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 187016456959197803248747733 4383198209981198513642525)
                    ·
                      refine ⟨1643699328742949442615947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383198209981198513642525 1643699328742949442615947)
                      ·
                        rfl

theorem cell23_3201093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_3201093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201093 prefixEnd_3201093 := by exact prefixLift 3201093
  have htrace : WordTrace (prefixWord ++ tailWord_3201093) baseStart_3201093 baseEnd_3201093 := by
    simpa [prefixWord, tailWord_3201093, baseEnd_3201093] using wordTrace_append hprefix tailTrace_3201093
  have hstable : (prefixWord ++ tailWord_3201093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201093).length < 2 ^ (prefixWord ++ tailWord_3201093).sum := by decide
  have hdescent : baseEnd_3201093 < baseStart_3201093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201160 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3201160 : Nat := 118140960795 + 3201160 * 2 ^ 59
def prefixEnd_3201160 : Nat := 4983230072969 + 3 ^ 40 * 3201160 * 2
def baseEnd_3201160 : Nat := 547911243982266893492713

theorem tailTrace_3201160 : CollatzResearch.WordTrace tailWord_3201160 prefixEnd_3201160 547911243982266893492713 := by
  unfold tailWord_3201160
  simp only [CollatzResearch.WordTrace]
  refine ⟨58377948541375754723468467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77837264721834339631291289 58377948541375754723468467)
  ·
    refine ⟨87566922812063632085202701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58377948541375754723468467 87566922812063632085202701)
    ·
      refine ⟨32837596054523862031951013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87566922812063632085202701 32837596054523862031951013)
      ·
        refine ⟨6157049260223224130990815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32837596054523862031951013 6157049260223224130990815)
        ·
          refine ⟨9235573890334836196486223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157049260223224130990815 9235573890334836196486223)
          ·
            refine ⟨13853360835502254294729335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9235573890334836196486223 13853360835502254294729335)
            ·
              refine ⟨20780041253253381442094003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853360835502254294729335 20780041253253381442094003)
              ·
                refine ⟨31170061879880072163141005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20780041253253381442094003 31170061879880072163141005)
                ·
                  refine ⟨11688773204955027061177877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31170061879880072163141005 11688773204955027061177877)
                  ·
                    refine ⟨547911243982266893492713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11688773204955027061177877 547911243982266893492713)
                    ·
                      rfl

theorem cell23_3201160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3201160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201160 prefixEnd_3201160 := by exact prefixLift 3201160
  have htrace : WordTrace (prefixWord ++ tailWord_3201160) baseStart_3201160 baseEnd_3201160 := by
    simpa [prefixWord, tailWord_3201160, baseEnd_3201160] using wordTrace_append hprefix tailTrace_3201160
  have hstable : (prefixWord ++ tailWord_3201160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201160).length < 2 ^ (prefixWord ++ tailWord_3201160).sum := by decide
  have hdescent : baseEnd_3201160 < baseStart_3201160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201180 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3201180 : Nat := 118140960795 + 3201180 * 2 ^ 59
def prefixEnd_3201180 : Nat := 4983230072969 + 3 ^ 40 * 3201180 * 2
def baseEnd_3201180 : Nat := 1643744001559890602228047

theorem tailTrace_3201180 : CollatzResearch.WordTrace tailWord_3201180 prefixEnd_3201180 1643744001559890602228047 := by
  unfold tailWord_3201180
  simp only [CollatzResearch.WordTrace]
  refine ⟨58378313271339526431332497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77837751028452701908443329 58378313271339526431332497)
  ·
    refine ⟨43783734953504644823499373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58378313271339526431332497 43783734953504644823499373)
    ·
      refine ⟨16418900607564241808812265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43783734953504644823499373 16418900607564241808812265)
      ·
        refine ⟨12314175455673181356609199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16418900607564241808812265 12314175455673181356609199)
        ·
          refine ⟨18471263183509772034913799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12314175455673181356609199 18471263183509772034913799)
          ·
            refine ⟨27706894775264658052370699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18471263183509772034913799 27706894775264658052370699)
            ·
              refine ⟨41560342162896987078556049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27706894775264658052370699 41560342162896987078556049)
              ·
                refine ⟨31170256622172740308917037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41560342162896987078556049 31170256622172740308917037)
                ·
                  refine ⟨11688846233314777615843889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31170256622172740308917037 11688846233314777615843889)
                  ·
                    refine ⟨8766634674986083211882917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11688846233314777615843889 8766634674986083211882917)
                    ·
                      refine ⟨1643744001559890602228047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8766634674986083211882917 1643744001559890602228047)
                      ·
                        rfl

theorem cell23_3201180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3201180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201180 prefixEnd_3201180 := by exact prefixLift 3201180
  have htrace : WordTrace (prefixWord ++ tailWord_3201180) baseStart_3201180 baseEnd_3201180 := by
    simpa [prefixWord, tailWord_3201180, baseEnd_3201180] using wordTrace_append hprefix tailTrace_3201180
  have hstable : (prefixWord ++ tailWord_3201180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201180).length < 2 ^ (prefixWord ++ tailWord_3201180).sum := by decide
  have hdescent : baseEnd_3201180 < baseStart_3201180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201194 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3201194 : Nat := 118140960795 + 3201194 * 2 ^ 59
def prefixEnd_3201194 : Nat := 4983230072969 + 3 ^ 40 * 3201194 * 2
def baseEnd_3201194 : Nat := 547917063429684515817661

theorem tailTrace_3201194 : CollatzResearch.WordTrace tailWord_3201194 prefixEnd_3201194 547917063429684515817661 := by
  unfold tailWord_3201194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29189284291157083313418659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77838091443085555502449757 29189284291157083313418659)
  ·
    refine ⟨43783926436735624970127989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29189284291157083313418659 43783926436735624970127989)
    ·
      refine ⟨4104743103443964840949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43783926436735624970127989 4104743103443964840949499)
      ·
        refine ⟨6157114655165947261424249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104743103443964840949499 6157114655165947261424249)
        ·
          refine ⟨4617835991374460446068187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157114655165947261424249 4617835991374460446068187)
          ·
            refine ⟨6926753987061690669102281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617835991374460446068187 6926753987061690669102281)
            ·
              refine ⟨5195065490296268001826711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926753987061690669102281 5195065490296268001826711)
              ·
                refine ⟨7792598235444402002740067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195065490296268001826711 7792598235444402002740067)
                ·
                  refine ⟨11688897353166603004110101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792598235444402002740067 11688897353166603004110101)
                  ·
                    refine ⟨547917063429684515817661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11688897353166603004110101 547917063429684515817661)
                    ·
                      rfl

theorem cell23_3201194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3201194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201194 prefixEnd_3201194 := by exact prefixLift 3201194
  have htrace : WordTrace (prefixWord ++ tailWord_3201194) baseStart_3201194 baseEnd_3201194 := by
    simpa [prefixWord, tailWord_3201194, baseEnd_3201194] using wordTrace_append hprefix tailTrace_3201194
  have hstable : (prefixWord ++ tailWord_3201194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201194).length < 2 ^ (prefixWord ++ tailWord_3201194).sum := by decide
  have hdescent : baseEnd_3201194 < baseStart_3201194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201197 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3201197 : Nat := 118140960795 + 3201197 * 2 ^ 59
def prefixEnd_3201197 : Nat := 4983230072969 + 3 ^ 40 * 3201197 * 2
def baseEnd_3201197 : Nat := 1643752730731017035715469

theorem tailTrace_3201197 : CollatzResearch.WordTrace tailWord_3201197 prefixEnd_3201197 1643752730731017035715469 := by
  unfold tailWord_3201197
  simp only [CollatzResearch.WordTrace]
  refine ⟨116757246583617464766033845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77838164389078309844022563 116757246583617464766033845)
  ·
    refine ⟨10945991867214137321815673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116757246583617464766033845 10945991867214137321815673)
    ·
      refine ⟨8209493900410602991361755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10945991867214137321815673 8209493900410602991361755)
      ·
        refine ⟨12314240850615904487042633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209493900410602991361755 12314240850615904487042633)
        ·
          refine ⟨9235680637961928365281975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12314240850615904487042633 9235680637961928365281975)
          ·
            refine ⟨13853520956942892547922963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9235680637961928365281975 13853520956942892547922963)
            ·
              refine ⟨20780281435414338821884445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853520956942892547922963 20780281435414338821884445)
              ·
                refine ⟨7792605538280377058206667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20780281435414338821884445 7792605538280377058206667)
                ·
                  refine ⟨11688908307420565587310001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792605538280377058206667 11688908307420565587310001)
                  ·
                    refine ⟨8766681230565424190482501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11688908307420565587310001 8766681230565424190482501)
                    ·
                      refine ⟨1643752730731017035715469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8766681230565424190482501 1643752730731017035715469)
                      ·
                        rfl

theorem cell23_3201197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3201197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201197 prefixEnd_3201197 := by exact prefixLift 3201197
  have htrace : WordTrace (prefixWord ++ tailWord_3201197) baseStart_3201197 baseEnd_3201197 := by
    simpa [prefixWord, tailWord_3201197, baseEnd_3201197] using wordTrace_append hprefix tailTrace_3201197
  have hstable : (prefixWord ++ tailWord_3201197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201197).length < 2 ^ (prefixWord ++ tailWord_3201197).sum := by decide
  have hdescent : baseEnd_3201197 < baseStart_3201197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201201 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3201201 : Nat := 118140960795 + 3201201 * 2 ^ 59
def prefixEnd_3201201 : Nat := 4983230072969 + 3 ^ 40 * 3201201 * 2
def baseEnd_3201201 : Nat := 1643754784653635020065451

theorem tailTrace_3201201 : CollatzResearch.WordTrace tailWord_3201201 prefixEnd_3201201 1643754784653635020065451 := by
  unfold tailWord_3201201
  simp only [CollatzResearch.WordTrace]
  refine ⟨116757392475602973449179457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77838261650401982299452971 116757392475602973449179457)
  ·
    refine ⟨87568044356702230086884593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116757392475602973449179457 87568044356702230086884593)
    ·
      refine ⟨65676033267526672565163445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87568044356702230086884593 65676033267526672565163445)
      ·
        refine ⟨6157128118830625552984073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65676033267526672565163445 6157128118830625552984073)
        ·
          refine ⟨4617846089122969164738055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157128118830625552984073 4617846089122969164738055)
          ·
            refine ⟨6926769133684453747107083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617846089122969164738055 6926769133684453747107083)
            ·
              refine ⟨10390153700526680620660625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926769133684453747107083 10390153700526680620660625)
              ·
                refine ⟨7792615275395010465495469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390153700526680620660625 7792615275395010465495469)
                ·
                  refine ⟨2922230728273128924560801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7792615275395010465495469 2922230728273128924560801)
                  ·
                    refine ⟨2191673046204846693420601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922230728273128924560801 2191673046204846693420601)
                    ·
                      refine ⟨1643754784653635020065451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191673046204846693420601 1643754784653635020065451)
                      ·
                        rfl

theorem cell23_3201201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3201201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201201 prefixEnd_3201201 := by exact prefixLift 3201201
  have htrace : WordTrace (prefixWord ++ tailWord_3201201) baseStart_3201201 baseEnd_3201201 := by
    simpa [prefixWord, tailWord_3201201, baseEnd_3201201] using wordTrace_append hprefix tailTrace_3201201
  have hstable : (prefixWord ++ tailWord_3201201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201201).length < 2 ^ (prefixWord ++ tailWord_3201201).sum := by decide
  have hdescent : baseEnd_3201201 < baseStart_3201201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201203 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 7]
def baseStart_3201203 : Nat := 118140960795 + 3201203 * 2 ^ 59
def prefixEnd_3201203 : Nat := 4983230072969 + 3 ^ 40 * 3201203 * 2
def baseEnd_3201203 : Nat := 547918603871648004080147

theorem tailTrace_3201203 : CollatzResearch.WordTrace tailWord_3201203 prefixEnd_3201203 547918603871648004080147 := by
  unfold tailWord_3201203
  simp only [CollatzResearch.WordTrace]
  refine ⟨116757465421595727790752263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77838310281063818527168175 116757465421595727790752263)
  ·
    refine ⟨175136198132393591686128395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116757465421595727790752263 175136198132393591686128395)
    ·
      refine ⟨262704297198590387529192593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175136198132393591686128395 262704297198590387529192593)
      ·
        refine ⟨197028222898942790646894445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262704297198590387529192593 197028222898942790646894445)
        ·
          refine ⟨73885583587103546492585417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197028222898942790646894445 73885583587103546492585417)
          ·
            refine ⟨55414187690327659869439063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73885583587103546492585417 55414187690327659869439063)
            ·
              refine ⟨83121281535491489804158595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55414187690327659869439063 83121281535491489804158595)
              ·
                refine ⟨124681922303237234706237893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83121281535491489804158595 124681922303237234706237893)
                ·
                  refine ⟨23377860431856981507419605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124681922303237234706237893 23377860431856981507419605)
                  ·
                    refine ⟨547918603871648004080147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23377860431856981507419605 547918603871648004080147)
                    ·
                      rfl

theorem cell23_3201203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_3201203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201203 prefixEnd_3201203 := by exact prefixLift 3201203
  have htrace : WordTrace (prefixWord ++ tailWord_3201203) baseStart_3201203 baseEnd_3201203 := by
    simpa [prefixWord, tailWord_3201203, baseEnd_3201203] using wordTrace_append hprefix tailTrace_3201203
  have hstable : (prefixWord ++ tailWord_3201203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201203).length < 2 ^ (prefixWord ++ tailWord_3201203).sum := by decide
  have hdescent : baseEnd_3201203 < baseStart_3201203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201218 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_3201218 : Nat := 118140960795 + 3201218 * 2 ^ 59
def prefixEnd_3201218 : Nat := 4983230072969 + 3 ^ 40 * 3201218 * 2
def baseEnd_3201218 : Nat := 1643763513824761453552873

theorem tailTrace_3201218 : CollatzResearch.WordTrace tailWord_3201218 prefixEnd_3201218 1643763513824761453552873 := by
  unfold tailWord_3201218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29189503129135346338137077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77838675011027590235032205 29189503129135346338137077)
  ·
    refine ⟨2736515918356438719200351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29189503129135346338137077 2736515918356438719200351)
    ·
      refine ⟨4104773877534658078800527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736515918356438719200351 4104773877534658078800527)
      ·
        refine ⟨6157160816301987118200791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104773877534658078800527 6157160816301987118200791)
        ·
          refine ⟨9235741224452980677301187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157160816301987118200791 9235741224452980677301187)
          ·
            refine ⟨13853611836679471015951781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9235741224452980677301187 13853611836679471015951781)
            ·
              refine ⟨2597552219377400815490959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13853611836679471015951781 2597552219377400815490959)
              ·
                refine ⟨3896328329066101223236439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597552219377400815490959 3896328329066101223236439)
                ·
                  refine ⟨5844492493599151834854659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896328329066101223236439 5844492493599151834854659)
                  ·
                    refine ⟨8766738740398727752281989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5844492493599151834854659 8766738740398727752281989)
                    ·
                      refine ⟨1643763513824761453552873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8766738740398727752281989 1643763513824761453552873)
                      ·
                        rfl

theorem cell23_3201218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_3201218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201218 prefixEnd_3201218 := by exact prefixLift 3201218
  have htrace : WordTrace (prefixWord ++ tailWord_3201218) baseStart_3201218 baseEnd_3201218 := by
    simpa [prefixWord, tailWord_3201218, baseEnd_3201218] using wordTrace_append hprefix tailTrace_3201218
  have hstable : (prefixWord ++ tailWord_3201218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201218).length < 2 ^ (prefixWord ++ tailWord_3201218).sum := by decide
  have hdescent : baseEnd_3201218 < baseStart_3201218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201228 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_3201228 : Nat := 118140960795 + 3201228 * 2 ^ 59
def prefixEnd_3201228 : Nat := 4983230072969 + 3 ^ 40 * 3201228 * 2
def baseEnd_3201228 : Nat := 547922882877102138142609

theorem tailTrace_3201228 : CollatzResearch.WordTrace tailWord_3201228 prefixEnd_3201228 547922882877102138142609 := by
  unfold tailWord_3201228
  simp only [CollatzResearch.WordTrace]
  refine ⟨58379188623252578530206169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77838918164336771373608225 58379188623252578530206169)
  ·
    refine ⟨43784391467439433897654627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58379188623252578530206169 43784391467439433897654627)
    ·
      refine ⟨65676587201159150846481941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43784391467439433897654627 65676587201159150846481941)
      ·
        refine ⟨3078590025054335195928841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65676587201159150846481941 3078590025054335195928841)
        ·
          refine ⟨2308942518790751396946631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078590025054335195928841 2308942518790751396946631)
          ·
            refine ⟨3463413778186127095419947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308942518790751396946631 3463413778186127095419947)
            ·
              refine ⟨5195120667279190643129921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463413778186127095419947 5195120667279190643129921)
              ·
                refine ⟨3896340500459392982347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195120667279190643129921 3896340500459392982347441)
                ·
                  refine ⟨2922255375344544736760581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896340500459392982347441 2922255375344544736760581)
                  ·
                    refine ⟨547922882877102138142609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922255375344544736760581 547922882877102138142609)
                    ·
                      rfl

theorem cell23_3201228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_3201228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201228 prefixEnd_3201228 := by exact prefixLift 3201228
  have htrace : WordTrace (prefixWord ++ tailWord_3201228) baseStart_3201228 baseEnd_3201228 := by
    simpa [prefixWord, tailWord_3201228, baseEnd_3201228] using wordTrace_append hprefix tailTrace_3201228
  have hstable : (prefixWord ++ tailWord_3201228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201228).length < 2 ^ (prefixWord ++ tailWord_3201228).sum := by decide
  have hdescent : baseEnd_3201228 < baseStart_3201228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201234 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3201234 : Nat := 118140960795 + 3201234 * 2 ^ 59
def prefixEnd_3201234 : Nat := 4983230072969 + 3 ^ 40 * 3201234 * 2
def baseEnd_3201234 : Nat := 1643771729515233390952799

theorem tailTrace_3201234 : CollatzResearch.WordTrace tailWord_3201234 prefixEnd_3201234 1643771729515233390952799 := by
  unfold tailWord_3201234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29189649021120855021282689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77839064056322280056753837 29189649021120855021282689)
  ·
    refine ⟨21892236765840641265962017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29189649021120855021282689 21892236765840641265962017)
    ·
      refine ⟨16419177574380480949471513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21892236765840641265962017 16419177574380480949471513)
      ·
        refine ⟨12314383180785360712103635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16419177574380480949471513 12314383180785360712103635)
        ·
          refine ⟨18471574771178041068155453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12314383180785360712103635 18471574771178041068155453)
          ·
            refine ⟨6926840539191765400558295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18471574771178041068155453 6926840539191765400558295)
            ·
              refine ⟨10390260808787648100837443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926840539191765400558295 10390260808787648100837443)
              ·
                refine ⟨15585391213181472151256165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390260808787648100837443 15585391213181472151256165)
                ·
                  refine ⟨2922260852471526028360531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15585391213181472151256165 2922260852471526028360531)
                  ·
                    refine ⟨4383391278707289042540797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2922260852471526028360531 4383391278707289042540797)
                    ·
                      refine ⟨1643771729515233390952799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383391278707289042540797 1643771729515233390952799)
                      ·
                        rfl

theorem cell23_3201234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3201234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201234 prefixEnd_3201234 := by exact prefixLift 3201234
  have htrace : WordTrace (prefixWord ++ tailWord_3201234) baseStart_3201234 baseEnd_3201234 := by
    simpa [prefixWord, tailWord_3201234, baseEnd_3201234] using wordTrace_append hprefix tailTrace_3201234
  have hstable : (prefixWord ++ tailWord_3201234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201234).length < 2 ^ (prefixWord ++ tailWord_3201234).sum := by decide
  have hdescent : baseEnd_3201234 < baseStart_3201234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201251 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3201251 : Nat := 118140960795 + 3201251 * 2 ^ 59
def prefixEnd_3201251 : Nat := 4983230072969 + 3 ^ 40 * 3201251 * 2
def baseEnd_3201251 : Nat := 1643780458686359824440221

theorem tailTrace_3201251 : CollatzResearch.WordTrace tailWord_3201251 prefixEnd_3201251 1643780458686359824440221 := by
  unfold tailWord_3201251
  simp only [CollatzResearch.WordTrace]
  refine ⟨116759216125421831988499607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77839477416947887992333071 116759216125421831988499607)
  ·
    refine ⟨175138824188132747982749411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116759216125421831988499607 175138824188132747982749411)
    ·
      refine ⟨262708236282199121974124117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175138824188132747982749411 262708236282199121974124117)
      ·
        refine ⟨3078612143932020960634267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 262708236282199121974124117 3078612143932020960634267)
        ·
          refine ⟨4617918215898031440951401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078612143932020960634267 4617918215898031440951401)
          ·
            refine ⟨3463438661923523580713551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617918215898031440951401 3463438661923523580713551)
            ·
              refine ⟨5195157992885285371070327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463438661923523580713551 5195157992885285371070327)
              ·
                refine ⟨7792736989327928056605491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195157992885285371070327 7792736989327928056605491)
                ·
                  refine ⟨11689105483991892084908237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792736989327928056605491 11689105483991892084908237)
                  ·
                    refine ⟨4383414556496959531840589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11689105483991892084908237 4383414556496959531840589)
                    ·
                      refine ⟨1643780458686359824440221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383414556496959531840589 1643780458686359824440221)
                      ·
                        rfl

theorem cell23_3201251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3201251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201251 prefixEnd_3201251 := by exact prefixLift 3201251
  have htrace : WordTrace (prefixWord ++ tailWord_3201251) baseStart_3201251 baseEnd_3201251 := by
    simpa [prefixWord, tailWord_3201251, baseEnd_3201251] using wordTrace_append hprefix tailTrace_3201251
  have hstable : (prefixWord ++ tailWord_3201251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201251).length < 2 ^ (prefixWord ++ tailWord_3201251).sum := by decide
  have hdescent : baseEnd_3201251 < baseStart_3201251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201260 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3201260 : Nat := 118140960795 + 3201260 * 2 ^ 59
def prefixEnd_3201260 : Nat := 4983230072969 + 3 ^ 40 * 3201260 * 2
def baseEnd_3201260 : Nat := 1643785080012250289227679

theorem tailTrace_3201260 : CollatzResearch.WordTrace tailWord_3201260 prefixEnd_3201260 1643785080012250289227679 := by
  unfold tailWord_3201260
  simp only [CollatzResearch.WordTrace]
  refine ⟨58379772191194613262788617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77839696254926151017051489 58379772191194613262788617)
  ·
    refine ⟨43784829143395959947091463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58379772191194613262788617 43784829143395959947091463)
    ·
      refine ⟨65677243715093939920637195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43784829143395959947091463 65677243715093939920637195)
      ·
        refine ⟨98515865572640909880955793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65677243715093939920637195 98515865572640909880955793)
        ·
          refine ⟨73886899179480682410716845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98515865572640909880955793 73886899179480682410716845)
          ·
            refine ⟨27707587192305255904018817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73886899179480682410716845 27707587192305255904018817)
            ·
              refine ⟨20780690394228941928014113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27707587192305255904018817 20780690394228941928014113)
              ·
                refine ⟨15585517795671706446010585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20780690394228941928014113 15585517795671706446010585)
                ·
                  refine ⟨11689138346753779834507939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15585517795671706446010585 11689138346753779834507939)
                  ·
                    refine ⟨17533707520130669751761909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11689138346753779834507939 17533707520130669751761909)
                    ·
                      refine ⟨1643785080012250289227679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17533707520130669751761909 1643785080012250289227679)
                      ·
                        rfl

theorem cell23_3201260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3201260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201260 prefixEnd_3201260 := by exact prefixLift 3201260
  have htrace : WordTrace (prefixWord ++ tailWord_3201260) baseStart_3201260 baseEnd_3201260 := by
    simpa [prefixWord, tailWord_3201260, baseEnd_3201260] using wordTrace_append hprefix tailTrace_3201260
  have hstable : (prefixWord ++ tailWord_3201260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201260).length < 2 ^ (prefixWord ++ tailWord_3201260).sum := by decide
  have hdescent : baseEnd_3201260 < baseStart_3201260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201274 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2]
def baseStart_3201274 : Nat := 118140960795 + 3201274 * 2 ^ 59
def prefixEnd_3201274 : Nat := 4983230072969 + 3 ^ 40 * 3201274 * 2
def baseEnd_3201274 : Nat := 1643792268741413234452615

theorem tailTrace_3201274 : CollatzResearch.WordTrace tailWord_3201274 prefixEnd_3201274 1643792268741413234452615 := by
  unfold tailWord_3201274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29190013751084626729146719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77840036669559004611057917 29190013751084626729146719)
  ·
    refine ⟨43785020626626940093720079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29190013751084626729146719 43785020626626940093720079)
    ·
      refine ⟨65677530939940410140580119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43785020626626940093720079 65677530939940410140580119)
      ·
        refine ⟨98516296409910615210870179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65677530939940410140580119 98516296409910615210870179)
        ·
          refine ⟨147774444614865922816305269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98516296409910615210870179 147774444614865922816305269)
          ·
            refine ⟨13853854182643680264028619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147774444614865922816305269 13853854182643680264028619)
            ·
              refine ⟨20780781273965520396042929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853854182643680264028619 20780781273965520396042929)
              ·
                refine ⟨15585585955474140297032197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20780781273965520396042929 15585585955474140297032197)
                ·
                  refine ⟨2922297366651401305693537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15585585955474140297032197 2922297366651401305693537)
                  ·
                    refine ⟨2191723024988550979270153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922297366651401305693537 2191723024988550979270153)
                    ·
                      refine ⟨1643792268741413234452615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191723024988550979270153 1643792268741413234452615)
                      ·
                        rfl

theorem cell23_3201274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2].length) (baseStart_3201274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201274 prefixEnd_3201274 := by exact prefixLift 3201274
  have htrace : WordTrace (prefixWord ++ tailWord_3201274) baseStart_3201274 baseEnd_3201274 := by
    simpa [prefixWord, tailWord_3201274, baseEnd_3201274] using wordTrace_append hprefix tailTrace_3201274
  have hstable : (prefixWord ++ tailWord_3201274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201274).length < 2 ^ (prefixWord ++ tailWord_3201274).sum := by decide
  have hdescent : baseEnd_3201274 < baseStart_3201274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201297 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 7]
def baseStart_3201297 : Nat := 118140960795 + 3201297 * 2 ^ 59
def prefixEnd_3201297 : Nat := 4983230072969 + 3 ^ 40 * 3201297 * 2
def baseEnd_3201297 : Nat := 182644897644051849385001

theorem tailTrace_3201297 : CollatzResearch.WordTrace tailWord_3201297 prefixEnd_3201297 182644897644051849385001 := by
  unfold tailWord_3201297
  simp only [CollatzResearch.WordTrace]
  refine ⟨116760893883255181844674145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77840595922170121229782763 116760893883255181844674145)
  ·
    refine ⟨87570670412441386383505609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116760893883255181844674145 87570670412441386383505609)
    ·
      refine ⟨65678002809331039787629207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87570670412441386383505609 65678002809331039787629207)
      ·
        refine ⟨98517004213996559681443811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65678002809331039787629207 98517004213996559681443811)
        ·
          refine ⟨147775506320994839522165717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98517004213996559681443811 147775506320994839522165717)
          ·
            refine ⟨3463488429398316551300759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147775506320994839522165717 3463488429398316551300759)
            ·
              refine ⟨5195232644097474826951139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463488429398316551300759 5195232644097474826951139)
              ·
                refine ⟨7792848966146212240426709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195232644097474826951139 7792848966146212240426709)
                ·
                  refine ⟨182644897644051849385001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7792848966146212240426709 182644897644051849385001)
                  ·
                    rfl

theorem cell23_3201297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_3201297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201297 prefixEnd_3201297 := by exact prefixLift 3201297
  have htrace : WordTrace (prefixWord ++ tailWord_3201297) baseStart_3201297 baseEnd_3201297 := by
    simpa [prefixWord, tailWord_3201297, baseEnd_3201297] using wordTrace_append hprefix tailTrace_3201297
  have hstable : (prefixWord ++ tailWord_3201297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201297).length < 2 ^ (prefixWord ++ tailWord_3201297).sum := by decide
  have hdescent : baseEnd_3201297 < baseStart_3201297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201337 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3201337 : Nat := 118140960795 + 3201337 * 2 ^ 59
def prefixEnd_3201337 : Nat := 4983230072969 + 3 ^ 40 * 3201337 * 2
def baseEnd_3201337 : Nat := 1643824618022646487964825

theorem tailTrace_3201337 : CollatzResearch.WordTrace tailWord_3201337 prefixEnd_3201337 1643824618022646487964825 := by
  unfold tailWord_3201337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116762352803110268676130265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77841568535406845784086843 116762352803110268676130265)
  ·
    refine ⟨87571764602332701507097699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116762352803110268676130265 87571764602332701507097699)
    ·
      refine ⟨131357646903499052260646549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87571764602332701507097699 131357646903499052260646549)
      ·
        refine ⟨6157389698601518074717807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131357646903499052260646549 6157389698601518074717807)
        ·
          refine ⟨9236084547902277112076711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157389698601518074717807 9236084547902277112076711)
          ·
            refine ⟨13854126821853415668115067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9236084547902277112076711 13854126821853415668115067)
            ·
              refine ⟨20781190232780123502172601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13854126821853415668115067 20781190232780123502172601)
              ·
                refine ⟨15585892674585092626629451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20781190232780123502172601 15585892674585092626629451)
                ·
                  refine ⟨23378839011877638939944177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15585892674585092626629451 23378839011877638939944177)
                  ·
                    refine ⟨17534129258908229204958133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23378839011877638939944177 17534129258908229204958133)
                    ·
                      refine ⟨1643824618022646487964825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17534129258908229204958133 1643824618022646487964825)
                      ·
                        rfl

theorem cell23_3201337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3201337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201337 prefixEnd_3201337 := by exact prefixLift 3201337
  have htrace : WordTrace (prefixWord ++ tailWord_3201337) baseStart_3201337 baseEnd_3201337 := by
    simpa [prefixWord, tailWord_3201337, baseEnd_3201337] using wordTrace_append hprefix tailTrace_3201337
  have hstable : (prefixWord ++ tailWord_3201337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201337).length < 2 ^ (prefixWord ++ tailWord_3201337).sum := by decide
  have hdescent : baseEnd_3201337 < baseStart_3201337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201347 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4]
def baseStart_3201347 : Nat := 118140960795 + 3201347 * 2 ^ 59
def prefixEnd_3201347 : Nat := 4983230072969 + 3 ^ 40 * 3201347 * 2
def baseEnd_3201347 : Nat := 1643829752829191448839779

theorem tailTrace_3201347 : CollatzResearch.WordTrace tailWord_3201347 prefixEnd_3201347 1643829752829191448839779 := by
  unfold tailWord_3201347
  simp only [CollatzResearch.WordTrace]
  refine ⟨116762717533074040383994295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77841811688716026922662863 116762717533074040383994295)
  ·
    refine ⟨175144076299611060575991443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116762717533074040383994295 175144076299611060575991443)
    ·
      refine ⟨262716114449416590863987165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175144076299611060575991443 262716114449416590863987165)
      ·
        refine ⟨98518542918531221573995187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262716114449416590863987165 98518542918531221573995187)
        ·
          refine ⟨147777814377796832360992781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98518542918531221573995187 147777814377796832360992781)
          ·
            refine ⟨55416680391673812135372293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147777814377796832360992781 55416680391673812135372293)
            ·
              refine ⟨10390627573438839775382305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55416680391673812135372293 10390627573438839775382305)
              ·
                refine ⟨7792970680079129831536729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390627573438839775382305 7792970680079129831536729)
                ·
                  refine ⟨5844728010059347373652547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7792970680079129831536729 5844728010059347373652547)
                  ·
                    refine ⟨8767092015089021060478821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5844728010059347373652547 8767092015089021060478821)
                    ·
                      refine ⟨1643829752829191448839779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8767092015089021060478821 1643829752829191448839779)
                      ·
                        rfl

theorem cell23_3201347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_3201347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201347 prefixEnd_3201347 := by exact prefixLift 3201347
  have htrace : WordTrace (prefixWord ++ tailWord_3201347) baseStart_3201347 baseEnd_3201347 := by
    simpa [prefixWord, tailWord_3201347, baseEnd_3201347] using wordTrace_append hprefix tailTrace_3201347
  have hstable : (prefixWord ++ tailWord_3201347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201347).length < 2 ^ (prefixWord ++ tailWord_3201347).sum := by decide
  have hdescent : baseEnd_3201347 < baseStart_3201347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201364 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_3201364 : Nat := 118140960795 + 3201364 * 2 ^ 59
def prefixEnd_3201364 : Nat := 4983230072969 + 3 ^ 40 * 3201364 * 2
def baseEnd_3201364 : Nat := 1643838482000317882327201

theorem tailTrace_3201364 : CollatzResearch.WordTrace tailWord_3201364 prefixEnd_3201364 1643838482000317882327201 := by
  unfold tailWord_3201364
  simp only [CollatzResearch.WordTrace]
  refine ⟨58381668787006226143681573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77842225049341634858242097 58381668787006226143681573)
  ·
    refine ⟨10946562897563667401940295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58381668787006226143681573 10946562897563667401940295)
    ·
      refine ⟨16419844346345501102910443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10946562897563667401940295 16419844346345501102910443)
      ·
        refine ⟨24629766519518251654365665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16419844346345501102910443 24629766519518251654365665)
        ·
          refine ⟨18472324889638688740774249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24629766519518251654365665 18472324889638688740774249)
          ·
            refine ⟨13854243667229016555580687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18472324889638688740774249 13854243667229016555580687)
            ·
              refine ⟨20781365500843524833371031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13854243667229016555580687 20781365500843524833371031)
              ·
                refine ⟨31172048251265287250056547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20781365500843524833371031 31172048251265287250056547)
                ·
                  refine ⟨46758072376897930875084821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31172048251265287250056547 46758072376897930875084821)
                  ·
                    refine ⟨2191784642667090509769601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46758072376897930875084821 2191784642667090509769601)
                    ·
                      refine ⟨1643838482000317882327201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191784642667090509769601 1643838482000317882327201)
                      ·
                        rfl

theorem cell23_3201364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_3201364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201364 prefixEnd_3201364 := by exact prefixLift 3201364
  have htrace : WordTrace (prefixWord ++ tailWord_3201364) baseStart_3201364 baseEnd_3201364 := by
    simpa [prefixWord, tailWord_3201364, baseEnd_3201364] using wordTrace_append hprefix tailTrace_3201364
  have hstable : (prefixWord ++ tailWord_3201364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201364).length < 2 ^ (prefixWord ++ tailWord_3201364).sum := by decide
  have hdescent : baseEnd_3201364 < baseStart_3201364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201367 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_3201367 : Nat := 118140960795 + 3201367 * 2 ^ 59
def prefixEnd_3201367 : Nat := 4983230072969 + 3 ^ 40 * 3201367 * 2
def baseEnd_3201367 : Nat := 1643840022442281370589687

theorem tailTrace_3201367 : CollatzResearch.WordTrace tailWord_3201367 prefixEnd_3201367 1643840022442281370589687 := by
  unfold tailWord_3201367
  simp only [CollatzResearch.WordTrace]
  refine ⟨116763446993001583799722355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77842297995334389199814903 116763446993001583799722355)
  ·
    refine ⟨175145170489502375699583533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116763446993001583799722355 175145170489502375699583533)
    ·
      refine ⟨65679438933563390887343825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175145170489502375699583533 65679438933563390887343825)
      ·
        refine ⟨49259579200172543165507869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65679438933563390887343825 49259579200172543165507869)
        ·
          refine ⟨18472342200064703687065451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49259579200172543165507869 18472342200064703687065451)
          ·
            refine ⟨27708513300097055530598177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18472342200064703687065451 27708513300097055530598177)
            ·
              refine ⟨20781384975072791647948633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27708513300097055530598177 20781384975072791647948633)
              ·
                refine ⟨15586038731304593735961475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20781384975072791647948633 15586038731304593735961475)
                ·
                  refine ⟨23379058096956890603942213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15586038731304593735961475 23379058096956890603942213)
                  ·
                    refine ⟨4383573393179416988239165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23379058096956890603942213 4383573393179416988239165)
                    ·
                      refine ⟨1643840022442281370589687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383573393179416988239165 1643840022442281370589687)
                      ·
                        rfl

theorem cell23_3201367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_3201367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201367 prefixEnd_3201367 := by exact prefixLift 3201367
  have htrace : WordTrace (prefixWord ++ tailWord_3201367) baseStart_3201367 baseEnd_3201367 := by
    simpa [prefixWord, tailWord_3201367, baseEnd_3201367] using wordTrace_append hprefix tailTrace_3201367
  have hstable : (prefixWord ++ tailWord_3201367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201367).length < 2 ^ (prefixWord ++ tailWord_3201367).sum := by decide
  have hdescent : baseEnd_3201367 < baseStart_3201367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201370 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 10]
def baseStart_3201370 : Nat := 118140960795 + 3201370 * 2 ^ 59
def prefixEnd_3201370 : Nat := 4983230072969 + 3 ^ 40 * 3201370 * 2
def baseEnd_3201370 : Nat := 182649062542693873205797

theorem tailTrace_3201370 : CollatzResearch.WordTrace tailWord_3201370 prefixEnd_3201370 182649062542693873205797 := by
  unfold tailWord_3201370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29190889102997678828020391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77842370941327143541387709 29190889102997678828020391)
  ·
    refine ⟨43786333654496518242030587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29190889102997678828020391 43786333654496518242030587)
    ·
      refine ⟨65679500481744777363045881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43786333654496518242030587 65679500481744777363045881)
      ·
        refine ⟨49259625361308583022284411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65679500481744777363045881 49259625361308583022284411)
        ·
          refine ⟨73889438041962874533426617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49259625361308583022284411 73889438041962874533426617)
          ·
            refine ⟨55417078531472155900069963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73889438041962874533426617 55417078531472155900069963)
            ·
              refine ⟨83125617797208233850104945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55417078531472155900069963 83125617797208233850104945)
              ·
                refine ⟨62344213347906175387578709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83125617797208233850104945 62344213347906175387578709)
                ·
                  refine ⟨182649062542693873205797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 62344213347906175387578709 182649062542693873205797)
                  ·
                    rfl

theorem cell23_3201370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 10].length) (baseStart_3201370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201370 prefixEnd_3201370 := by exact prefixLift 3201370
  have htrace : WordTrace (prefixWord ++ tailWord_3201370) baseStart_3201370 baseEnd_3201370 := by
    simpa [prefixWord, tailWord_3201370, baseEnd_3201370] using wordTrace_append hprefix tailTrace_3201370
  have hstable : (prefixWord ++ tailWord_3201370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201370).length < 2 ^ (prefixWord ++ tailWord_3201370).sum := by decide
  have hdescent : baseEnd_3201370 < baseStart_3201370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201384 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3201384 : Nat := 118140960795 + 3201384 * 2 ^ 59
def prefixEnd_3201384 : Nat := 4983230072969 + 3 ^ 40 * 3201384 * 2
def baseEnd_3201384 : Nat := 1643848751613407804077109

theorem tailTrace_3201384 : CollatzResearch.WordTrace tailWord_3201384 prefixEnd_3201384 1643848751613407804077109 := by
  unfold tailWord_3201384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58382033516969997851545603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77842711355959997135394137 58382033516969997851545603)
  ·
    refine ⟨87573050275454996777318405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58382033516969997851545603 87573050275454996777318405)
    ·
      refine ⟨16419946926647811895747201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87573050275454996777318405 16419946926647811895747201)
      ·
        refine ⟨12314960194985858921810401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16419946926647811895747201 12314960194985858921810401)
        ·
          refine ⟨9236220146239394191357801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12314960194985858921810401 9236220146239394191357801)
          ·
            refine ⟨6927165109679545643518351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9236220146239394191357801 6927165109679545643518351)
            ·
              refine ⟨10390747664519318465277527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927165109679545643518351 10390747664519318465277527)
              ·
                refine ⟨15586121496778977697916291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390747664519318465277527 15586121496778977697916291)
                ·
                  refine ⟨23379182245168466546874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15586121496778977697916291 23379182245168466546874437)
                  ·
                    refine ⟨4383596670969087477538957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23379182245168466546874437 4383596670969087477538957)
                    ·
                      refine ⟨1643848751613407804077109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383596670969087477538957 1643848751613407804077109)
                      ·
                        rfl

theorem cell23_3201384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3201384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201384 prefixEnd_3201384 := by exact prefixLift 3201384
  have htrace : WordTrace (prefixWord ++ tailWord_3201384) baseStart_3201384 baseEnd_3201384 := by
    simpa [prefixWord, tailWord_3201384, baseEnd_3201384] using wordTrace_append hprefix tailTrace_3201384
  have hstable : (prefixWord ++ tailWord_3201384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201384).length < 2 ^ (prefixWord ++ tailWord_3201384).sum := by decide
  have hdescent : baseEnd_3201384 < baseStart_3201384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201434 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 1, 5]
def baseStart_3201434 : Nat := 118140960795 + 3201434 * 2 ^ 59
def prefixEnd_3201434 : Nat := 4983230072969 + 3 ^ 40 * 3201434 * 2
def baseEnd_3201434 : Nat := 547958141882044202817293

theorem tailTrace_3201434 : CollatzResearch.WordTrace tailWord_3201434 prefixEnd_3201434 547958141882044202817293 := by
  unfold tailWord_3201434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29191472670939713560602839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77843927122505902828274237 29191472670939713560602839)
  ·
    refine ⟨43787209006409570340904259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29191472670939713560602839 43787209006409570340904259)
    ·
      refine ⟨65680813509614355511356389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43787209006409570340904259 65680813509614355511356389)
      ·
        refine ⟨12315152533052691658379323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65680813509614355511356389 12315152533052691658379323)
        ·
          refine ⟨18472728799579037487568985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315152533052691658379323 18472728799579037487568985)
          ·
            refine ⟨13854546599684278115676739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18472728799579037487568985 13854546599684278115676739)
            ·
              refine ⟨20781819899526417173515109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13854546599684278115676739 20781819899526417173515109)
              ·
                refine ⟨3896591231161203220034083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20781819899526417173515109 3896591231161203220034083)
                ·
                  refine ⟨5844886846741804830051125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896591231161203220034083 5844886846741804830051125)
                  ·
                    refine ⟨547958141882044202817293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5844886846741804830051125 547958141882044202817293)
                    ·
                      rfl

theorem cell23_3201434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_3201434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201434 prefixEnd_3201434 := by exact prefixLift 3201434
  have htrace : WordTrace (prefixWord ++ tailWord_3201434) baseStart_3201434 baseEnd_3201434 := by
    simpa [prefixWord, tailWord_3201434, baseEnd_3201434] using wordTrace_append hprefix tailTrace_3201434
  have hstable : (prefixWord ++ tailWord_3201434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201434).length < 2 ^ (prefixWord ++ tailWord_3201434).sum := by decide
  have hdescent : baseEnd_3201434 < baseStart_3201434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201464 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_3201464 : Nat := 118140960795 + 3201464 * 2 ^ 59
def prefixEnd_3201464 : Nat := 4983230072969 + 3 ^ 40 * 3201464 * 2
def baseEnd_3201464 : Nat := 547963276688589163692247

theorem tailTrace_3201464 : CollatzResearch.WordTrace tailWord_3201464 prefixEnd_3201464 547963276688589163692247 := by
  unfold tailWord_3201464
  simp only [CollatzResearch.WordTrace]
  refine ⟨58383492436825084683001723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77844656582433446244002297 58383492436825084683001723)
  ·
    refine ⟨87575238655237627024502585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58383492436825084683001723 87575238655237627024502585)
    ·
      refine ⟨65681428991428220268376939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87575238655237627024502585 65681428991428220268376939)
      ·
        refine ⟨98522143487142330402565409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65681428991428220268376939 98522143487142330402565409)
        ·
          refine ⟨73891607615356747801924057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98522143487142330402565409 73891607615356747801924057)
          ·
            refine ⟨55418705711517560851443043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73891607615356747801924057 55418705711517560851443043)
            ·
              refine ⟨83128058567276341277164565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55418705711517560851443043 83128058567276341277164565)
              ·
                refine ⟨3896627745341078497367089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83128058567276341277164565 3896627745341078497367089)
                ·
                  refine ⟨2922470809005808873025317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896627745341078497367089 2922470809005808873025317)
                  ·
                    refine ⟨547963276688589163692247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922470809005808873025317 547963276688589163692247)
                    ·
                      rfl

theorem cell23_3201464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_3201464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201464 prefixEnd_3201464 := by exact prefixLift 3201464
  have htrace : WordTrace (prefixWord ++ tailWord_3201464) baseStart_3201464 baseEnd_3201464 := by
    simpa [prefixWord, tailWord_3201464, baseEnd_3201464] using wordTrace_append hprefix tailTrace_3201464
  have hstable : (prefixWord ++ tailWord_3201464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201464).length < 2 ^ (prefixWord ++ tailWord_3201464).sum := by decide
  have hdescent : baseEnd_3201464 < baseStart_3201464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201465 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3201465 : Nat := 118140960795 + 3201465 * 2 ^ 59
def prefixEnd_3201465 : Nat := 4983230072969 + 3 ^ 40 * 3201465 * 2
def baseEnd_3201465 : Nat := 1643890343546421987164237

theorem tailTrace_3201465 : CollatzResearch.WordTrace tailWord_3201465 prefixEnd_3201465 1643890343546421987164237 := by
  unfold tailWord_3201465
  simp only [CollatzResearch.WordTrace]
  refine ⟨116767021346646546536789849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77844680897764364357859899 116767021346646546536789849)
  ·
    refine ⟨87575266009984909902592387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116767021346646546536789849 87575266009984909902592387)
    ·
      refine ⟨131362899014977364853888581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87575266009984909902592387 131362899014977364853888581)
      ·
        refine ⟨24630543565308255910104109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131362899014977364853888581 24630543565308255910104109)
        ·
          refine ⟨9236453836990595966289041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24630543565308255910104109 9236453836990595966289041)
          ·
            refine ⟨6927340377742946974716781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9236453836990595966289041 6927340377742946974716781)
            ·
              refine ⟨2597752641653605115518793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6927340377742946974716781 2597752641653605115518793)
              ·
                refine ⟨1948314481240203836639095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597752641653605115518793 1948314481240203836639095)
                ·
                  refine ⟨2922471721860305754958643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948314481240203836639095 2922471721860305754958643)
                  ·
                    refine ⟨4383707582790458632437965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2922471721860305754958643 4383707582790458632437965)
                    ·
                      refine ⟨1643890343546421987164237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383707582790458632437965 1643890343546421987164237)
                      ·
                        rfl

theorem cell23_3201465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3201465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201465 prefixEnd_3201465 := by exact prefixLift 3201465
  have htrace : WordTrace (prefixWord ++ tailWord_3201465) baseStart_3201465 baseEnd_3201465 := by
    simpa [prefixWord, tailWord_3201465, baseEnd_3201465] using wordTrace_append hprefix tailTrace_3201465
  have hstable : (prefixWord ++ tailWord_3201465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201465).length < 2 ^ (prefixWord ++ tailWord_3201465).sum := by decide
  have hdescent : baseEnd_3201465 < baseStart_3201465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201481 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 2, 4]
def baseStart_3201481 : Nat := 118140960795 + 3201481 * 2 ^ 59
def prefixEnd_3201481 : Nat := 4983230072969 + 3 ^ 40 * 3201481 * 2
def baseEnd_3201481 : Nat := 547966186412297974854721

theorem tailTrace_3201481 : CollatzResearch.WordTrace tailWord_3201481 prefixEnd_3201481 547966186412297974854721 := by
  unfold tailWord_3201481
  simp only [CollatzResearch.WordTrace]
  refine ⟨116767604914588581269372297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77845069943059054179581531 116767604914588581269372297)
  ·
    refine ⟨87575703685941435952029223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116767604914588581269372297 87575703685941435952029223)
    ·
      refine ⟨131363555528912153928043835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87575703685941435952029223 131363555528912153928043835)
      ·
        refine ⟨197045333293368230892065753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131363555528912153928043835 197045333293368230892065753)
        ·
          refine ⟨147783999970026173169049315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197045333293368230892065753 147783999970026173169049315)
          ·
            refine ⟨221675999955039259753573973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147783999970026173169049315 221675999955039259753573973)
            ·
              refine ⟨2597765624473116325237195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 221675999955039259753573973 2597765624473116325237195)
              ·
                refine ⟨3896648436709674487855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597765624473116325237195 3896648436709674487855793)
                ·
                  refine ⟨2922486327532255865891845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896648436709674487855793 2922486327532255865891845)
                  ·
                    refine ⟨547966186412297974854721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922486327532255865891845 547966186412297974854721)
                    ·
                      rfl

theorem cell23_3201481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_3201481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201481 prefixEnd_3201481 := by exact prefixLift 3201481
  have htrace : WordTrace (prefixWord ++ tailWord_3201481) baseStart_3201481 baseEnd_3201481 := by
    simpa [prefixWord, tailWord_3201481, baseEnd_3201481] using wordTrace_append hprefix tailTrace_3201481
  have hstable : (prefixWord ++ tailWord_3201481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201481).length < 2 ^ (prefixWord ++ tailWord_3201481).sum := by decide
  have hdescent : baseEnd_3201481 < baseStart_3201481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201494 : List Nat := [5, 2, 1, 1, 1, 1, 1, 11]
def baseStart_3201494 : Nat := 118140960795 + 3201494 * 2 ^ 59
def prefixEnd_3201494 : Nat := 4983230072969 + 3 ^ 40 * 3201494 * 2
def baseEnd_3201494 : Nat := 60885379055014902729689

theorem tailTrace_3201494 : CollatzResearch.WordTrace tailWord_3201494 prefixEnd_3201494 60885379055014902729689 := by
  unfold tailWord_3201494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298004941471342780599721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77845386042360989659730357 7298004941471342780599721)
  ·
    refine ⟨5473503706103507085449791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7298004941471342780599721 5473503706103507085449791)
    ·
      refine ⟨8210255559155260628174687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473503706103507085449791 8210255559155260628174687)
      ·
        refine ⟨12315383338732890942262031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210255559155260628174687 12315383338732890942262031)
        ·
          refine ⟨18473075008099336413393047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315383338732890942262031 18473075008099336413393047)
          ·
            refine ⟨27709612512149004620089571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18473075008099336413393047 27709612512149004620089571)
            ·
              refine ⟨41564418768223506930134357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27709612512149004620089571 41564418768223506930134357)
              ·
                refine ⟨60885379055014902729689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41564418768223506930134357 60885379055014902729689)
                ·
                  rfl

theorem cell23_3201494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_3201494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201494 prefixEnd_3201494 := by exact prefixLift 3201494
  have htrace : WordTrace (prefixWord ++ tailWord_3201494) baseStart_3201494 baseEnd_3201494 := by
    simpa [prefixWord, tailWord_3201494, baseEnd_3201494] using wordTrace_append hprefix tailTrace_3201494
  have hstable : (prefixWord ++ tailWord_3201494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201494).length < 2 ^ (prefixWord ++ tailWord_3201494).sum := by decide
  have hdescent : baseEnd_3201494 < baseStart_3201494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201504 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3201504 : Nat := 118140960795 + 3201504 * 2 ^ 59
def prefixEnd_3201504 : Nat := 4983230072969 + 3 ^ 40 * 3201504 * 2
def baseEnd_3201504 : Nat := 1643910369291947334576557

theorem tailTrace_3201504 : CollatzResearch.WordTrace tailWord_3201504 prefixEnd_3201504 1643910369291947334576557 := by
  unfold tailWord_3201504
  simp only [CollatzResearch.WordTrace]
  refine ⟨58384221896752628098729783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77845629195670170798306377 58384221896752628098729783)
  ·
    refine ⟨87576332845128942148094675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58384221896752628098729783 87576332845128942148094675)
    ·
      refine ⟨131364499267693413222142013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87576332845128942148094675 131364499267693413222142013)
      ·
        refine ⟨49261687225385029958303255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131364499267693413222142013 49261687225385029958303255)
        ·
          refine ⟨73892530838077544937454883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49261687225385029958303255 73892530838077544937454883)
          ·
            refine ⟨110838796257116317406182325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73892530838077544937454883 110838796257116317406182325)
            ·
              refine ⟨10391137149104654756829593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110838796257116317406182325 10391137149104654756829593)
              ·
                refine ⟨7793352861828491067622195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10391137149104654756829593 7793352861828491067622195)
                ·
                  refine ⟨11690029292742736601433293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793352861828491067622195 11690029292742736601433293)
                  ·
                    refine ⟨4383760984778526225537485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11690029292742736601433293 4383760984778526225537485)
                    ·
                      refine ⟨1643910369291947334576557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383760984778526225537485 1643910369291947334576557)
                      ·
                        rfl

theorem cell23_3201504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3201504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201504 prefixEnd_3201504 := by exact prefixLift 3201504
  have htrace : WordTrace (prefixWord ++ tailWord_3201504) baseStart_3201504 baseEnd_3201504 := by
    simpa [prefixWord, tailWord_3201504, baseEnd_3201504] using wordTrace_append hprefix tailTrace_3201504
  have hstable : (prefixWord ++ tailWord_3201504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201504).length < 2 ^ (prefixWord ++ tailWord_3201504).sum := by decide
  have hdescent : baseEnd_3201504 < baseStart_3201504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201522 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3201522 : Nat := 118140960795 + 3201522 * 2 ^ 59
def prefixEnd_3201522 : Nat := 4983230072969 + 3 ^ 40 * 3201522 * 2
def baseEnd_3201522 : Nat := 1643919611943728264151475

theorem tailTrace_3201522 : CollatzResearch.WordTrace tailWord_3201522 prefixEnd_3201522 1643919611943728264151475 := by
  unfold tailWord_3201522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29192275076860011317903705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77846066871626696847743213 29192275076860011317903705)
  ·
    refine ⟨21894206307645008488427779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29192275076860011317903705 21894206307645008488427779)
    ·
      refine ⟨32841309461467512732641669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894206307645008488427779 32841309461467512732641669)
      ·
        refine ⟨6157745524025158637370313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32841309461467512732641669 6157745524025158637370313)
        ·
          refine ⟨4618309143018868978027735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157745524025158637370313 4618309143018868978027735)
          ·
            refine ⟨6927463714528303467041603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618309143018868978027735 6927463714528303467041603)
            ·
              refine ⟨10391195571792455200562405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927463714528303467041603 10391195571792455200562405)
              ·
                refine ⟨1948349169711085350105451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10391195571792455200562405 1948349169711085350105451)
                ·
                  refine ⟨2922523754566628025158177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948349169711085350105451 2922523754566628025158177)
                  ·
                    refine ⟨2191892815924971018868633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922523754566628025158177 2191892815924971018868633)
                    ·
                      refine ⟨1643919611943728264151475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191892815924971018868633 1643919611943728264151475)
                      ·
                        rfl

theorem cell23_3201522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3201522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201522 prefixEnd_3201522 := by exact prefixLift 3201522
  have htrace : WordTrace (prefixWord ++ tailWord_3201522) baseStart_3201522 baseEnd_3201522 := by
    simpa [prefixWord, tailWord_3201522, baseEnd_3201522] using wordTrace_append hprefix tailTrace_3201522
  have hstable : (prefixWord ++ tailWord_3201522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201522).length < 2 ^ (prefixWord ++ tailWord_3201522).sum := by decide
  have hdescent : baseEnd_3201522 < baseStart_3201522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201561 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 6, 2, 2]
def baseStart_3201561 : Nat := 118140960795 + 3201561 * 2 ^ 59
def prefixEnd_3201561 : Nat := 4983230072969 + 3 ^ 40 * 3201561 * 2
def baseEnd_3201561 : Nat := 1643939637689253611563795

theorem tailTrace_3201561 : CollatzResearch.WordTrace tailWord_3201561 prefixEnd_3201561 1643939637689253611563795 := by
  unfold tailWord_3201561
  simp only [CollatzResearch.WordTrace]
  refine ⟨116770522754298754932284537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77847015169532503288189691 116770522754298754932284537)
  ·
    refine ⟨87577892065724066199213403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116770522754298754932284537 87577892065724066199213403)
    ·
      refine ⟨131366838098586099298820105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87577892065724066199213403 131366838098586099298820105)
      ·
        refine ⟨98525128573939574474115079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131366838098586099298820105 98525128573939574474115079)
        ·
          refine ⟨147787692860909361711172619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98525128573939574474115079 147787692860909361711172619)
          ·
            refine ⟨221681539291364042566758929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147787692860909361711172619 221681539291364042566758929)
            ·
              refine ⟨166261154468523031925069197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221681539291364042566758929 166261154468523031925069197)
              ·
                refine ⟨62347932925696136971900949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166261154468523031925069197 62347932925696136971900949)
                ·
                  refine ⟨2922559355892006420557857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62347932925696136971900949 2922559355892006420557857)
                  ·
                    refine ⟨2191919516919004815418393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922559355892006420557857 2191919516919004815418393)
                    ·
                      refine ⟨1643939637689253611563795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191919516919004815418393 1643939637689253611563795)
                      ·
                        rfl

theorem cell23_3201561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_3201561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201561 prefixEnd_3201561 := by exact prefixLift 3201561
  have htrace : WordTrace (prefixWord ++ tailWord_3201561) baseStart_3201561 baseEnd_3201561 := by
    simpa [prefixWord, tailWord_3201561, baseEnd_3201561] using wordTrace_append hprefix tailTrace_3201561
  have hstable : (prefixWord ++ tailWord_3201561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201561).length < 2 ^ (prefixWord ++ tailWord_3201561).sum := by decide
  have hdescent : baseEnd_3201561 < baseStart_3201561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201565 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_3201565 : Nat := 118140960795 + 3201565 * 2 ^ 59
def prefixEnd_3201565 : Nat := 4983230072969 + 3 ^ 40 * 3201565 * 2
def baseEnd_3201565 : Nat := 1643941691611871595913777

theorem tailTrace_3201565 : CollatzResearch.WordTrace tailWord_3201565 prefixEnd_3201565 1643941691611871595913777 := by
  unfold tailWord_3201565
  simp only [CollatzResearch.WordTrace]
  refine ⟨116770668646284263615430149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77847112430856175743620099 116770668646284263615430149)
  ·
    refine ⟨21894500371178299427893153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116770668646284263615430149 21894500371178299427893153)
    ·
      refine ⟨16420875278383724570919865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21894500371178299427893153 16420875278383724570919865)
      ·
        refine ⟨12315656458787793428189899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16420875278383724570919865 12315656458787793428189899)
        ·
          refine ⟨18473484688181690142284849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12315656458787793428189899 18473484688181690142284849)
          ·
            refine ⟨13855113516136267606713637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18473484688181690142284849 13855113516136267606713637)
            ·
              refine ⟨2597833784275550176258807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13855113516136267606713637 2597833784275550176258807)
              ·
                refine ⟨3896750676413325264388211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597833784275550176258807 3896750676413325264388211)
                ·
                  refine ⟨5845126014619987896582317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896750676413325264388211 5845126014619987896582317)
                  ·
                    refine ⟨2191922255482495461218369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5845126014619987896582317 2191922255482495461218369)
                    ·
                      refine ⟨1643941691611871595913777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2191922255482495461218369 1643941691611871595913777)
                      ·
                        rfl

theorem cell23_3201565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_3201565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201565 prefixEnd_3201565 := by exact prefixLift 3201565
  have htrace : WordTrace (prefixWord ++ tailWord_3201565) baseStart_3201565 baseEnd_3201565 := by
    simpa [prefixWord, tailWord_3201565, baseEnd_3201565] using wordTrace_append hprefix tailTrace_3201565
  have hstable : (prefixWord ++ tailWord_3201565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201565).length < 2 ^ (prefixWord ++ tailWord_3201565).sum := by decide
  have hdescent : baseEnd_3201565 < baseStart_3201565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201567 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 11]
def baseStart_3201567 : Nat := 118140960795 + 3201567 * 2 ^ 59
def prefixEnd_3201567 : Nat := 4983230072969 + 3 ^ 40 * 3201567 * 2
def baseEnd_3201567 : Nat := 182660302063686732009863

theorem tailTrace_3201567 : CollatzResearch.WordTrace tailWord_3201567 prefixEnd_3201567 182660302063686732009863 := by
  unfold tailWord_3201567
  simp only [CollatzResearch.WordTrace]
  refine ⟨116770741592277017957002955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77847161061518011971335303 116770741592277017957002955)
  ·
    refine ⟨175156112388415526935504433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116770741592277017957002955 175156112388415526935504433)
    ·
      refine ⟨131367084291311645201628325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175156112388415526935504433 131367084291311645201628325)
      ·
        refine ⟨24631328304620933475305311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131367084291311645201628325 24631328304620933475305311)
        ·
          refine ⟨36946992456931400212957967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24631328304620933475305311 36946992456931400212957967)
          ·
            refine ⟨55420488685397100319436951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36946992456931400212957967 55420488685397100319436951)
            ·
              refine ⟨83130733028095650479155427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55420488685397100319436951 83130733028095650479155427)
              ·
                refine ⟨124696099542143475718733141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83130733028095650479155427 124696099542143475718733141)
                ·
                  refine ⟨182660302063686732009863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 124696099542143475718733141 182660302063686732009863)
                  ·
                    rfl

theorem cell23_3201567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 11].length) (baseStart_3201567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201567 prefixEnd_3201567 := by exact prefixLift 3201567
  have htrace : WordTrace (prefixWord ++ tailWord_3201567) baseStart_3201567 baseEnd_3201567 := by
    simpa [prefixWord, tailWord_3201567, baseEnd_3201567] using wordTrace_append hprefix tailTrace_3201567
  have hstable : (prefixWord ++ tailWord_3201567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201567).length < 2 ^ (prefixWord ++ tailWord_3201567).sum := by decide
  have hdescent : baseEnd_3201567 < baseStart_3201567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201572 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3201572 : Nat := 118140960795 + 3201572 * 2 ^ 59
def prefixEnd_3201572 : Nat := 4983230072969 + 3 ^ 40 * 3201572 * 2
def baseEnd_3201572 : Nat := 1643945285976453068526245

theorem tailTrace_3201572 : CollatzResearch.WordTrace tailWord_3201572 prefixEnd_3201572 1643945285976453068526245 := by
  unfold tailWord_3201572
  simp only [CollatzResearch.WordTrace]
  refine ⟨58385461978629451905467485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77847282638172602540623313 58385461978629451905467485)
  ·
    refine ⟨21894548241986044464550307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58385461978629451905467485 21894548241986044464550307)
    ·
      refine ⟨32841822362979066696825461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894548241986044464550307 32841822362979066696825461)
      ·
        refine ⟨3078920846529287502827387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32841822362979066696825461 3078920846529287502827387)
        ·
          refine ⟨4618381269793931254241081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078920846529287502827387 4618381269793931254241081)
          ·
            refine ⟨3463785952345448440680811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618381269793931254241081 3463785952345448440680811)
            ·
              refine ⟨5195678928518172661021217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463785952345448440680811 5195678928518172661021217)
              ·
                refine ⟨3896759196388629495765913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195678928518172661021217 3896759196388629495765913)
                ·
                  refine ⟨2922569397291472121824435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896759196388629495765913 2922569397291472121824435)
                  ·
                    refine ⟨4383854095937208182736653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2922569397291472121824435 4383854095937208182736653)
                    ·
                      refine ⟨1643945285976453068526245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4383854095937208182736653 1643945285976453068526245)
                      ·
                        rfl

theorem cell23_3201572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3201572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201572 prefixEnd_3201572 := by exact prefixLift 3201572
  have htrace : WordTrace (prefixWord ++ tailWord_3201572) baseStart_3201572 baseEnd_3201572 := by
    simpa [prefixWord, tailWord_3201572, baseEnd_3201572] using wordTrace_append hprefix tailTrace_3201572
  have hstable : (prefixWord ++ tailWord_3201572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201572).length < 2 ^ (prefixWord ++ tailWord_3201572).sum := by decide
  have hdescent : baseEnd_3201572 < baseStart_3201572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201614 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3201614 : Nat := 118140960795 + 3201614 * 2 ^ 59
def prefixEnd_3201614 : Nat := 4983230072969 + 3 ^ 40 * 3201614 * 2
def baseEnd_3201614 : Nat := 547988950721313968067017

theorem tailTrace_3201614 : CollatzResearch.WordTrace tailWord_3201614 prefixEnd_3201614 547988950721313968067017 := by
  unfold tailWord_3201614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596556977888343122995487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77848303882071163322642597 14596556977888343122995487)
  ·
    refine ⟨21894835466832514684493231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596556977888343122995487 21894835466832514684493231)
    ·
      refine ⟨32842253200248772026739847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894835466832514684493231 32842253200248772026739847)
      ·
        refine ⟨49263379800373158040109771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32842253200248772026739847 49263379800373158040109771)
        ·
          refine ⟨73895069700559737060164657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49263379800373158040109771 73895069700559737060164657)
          ·
            refine ⟨55421302275419802795123493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73895069700559737060164657 55421302275419802795123493)
            ·
              refine ⟨10391494176641213024085655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55421302275419802795123493 10391494176641213024085655)
              ·
                refine ⟨15587241264961819536128483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10391494176641213024085655 15587241264961819536128483)
                ·
                  refine ⟨23380861897442729304192725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15587241264961819536128483 23380861897442729304192725)
                  ·
                    refine ⟨547988950721313968067017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23380861897442729304192725 547988950721313968067017)
                    ·
                      rfl

theorem cell23_3201614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3201614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201614 prefixEnd_3201614 := by exact prefixLift 3201614
  have htrace : WordTrace (prefixWord ++ tailWord_3201614) baseStart_3201614 baseEnd_3201614 := by
    simpa [prefixWord, tailWord_3201614, baseEnd_3201614] using wordTrace_append hprefix tailTrace_3201614
  have hstable : (prefixWord ++ tailWord_3201614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201614).length < 2 ^ (prefixWord ++ tailWord_3201614).sum := by decide
  have hdescent : baseEnd_3201614 < baseStart_3201614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201668 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3201668 : Nat := 118140960795 + 3201668 * 2 ^ 59
def prefixEnd_3201668 : Nat := 4983230072969 + 3 ^ 40 * 3201668 * 2
def baseEnd_3201668 : Nat := 1643994580119284692925803

theorem tailTrace_3201668 : CollatzResearch.WordTrace tailWord_3201668 prefixEnd_3201668 1643994580119284692925803 := by
  unfold tailWord_3201668
  simp only [CollatzResearch.WordTrace]
  refine ⟨58387212682455556103214829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77849616909940741470953105 58387212682455556103214829)
  ·
    refine ⟨21895204755920833538705561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58387212682455556103214829 21895204755920833538705561)
    ·
      refine ⟨16421403566940625154029171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21895204755920833538705561 16421403566940625154029171)
      ·
        refine ⟨24632105350410937731043757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16421403566940625154029171 24632105350410937731043757)
        ·
          refine ⟨9237039506404101649141409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24632105350410937731043757 9237039506404101649141409)
          ·
            refine ⟨6927779629803076236856057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9237039506404101649141409 6927779629803076236856057)
            ·
              refine ⟨5195834722352307177642043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927779629803076236856057 5195834722352307177642043)
              ·
                refine ⟨7793752083528460766463065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195834722352307177642043 7793752083528460766463065)
                ·
                  refine ⟨5845314062646345574847299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7793752083528460766463065 5845314062646345574847299)
                  ·
                    refine ⟨8767971093969518362270949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5845314062646345574847299 8767971093969518362270949)
                    ·
                      refine ⟨1643994580119284692925803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8767971093969518362270949 1643994580119284692925803)
                      ·
                        rfl

theorem cell23_3201668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3201668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201668 prefixEnd_3201668 := by exact prefixLift 3201668
  have htrace : WordTrace (prefixWord ++ tailWord_3201668) baseStart_3201668 baseEnd_3201668 := by
    simpa [prefixWord, tailWord_3201668, baseEnd_3201668] using wordTrace_append hprefix tailTrace_3201668
  have hstable : (prefixWord ++ tailWord_3201668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201668).length < 2 ^ (prefixWord ++ tailWord_3201668).sum := by decide
  have hdescent : baseEnd_3201668 < baseStart_3201668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201714 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_3201714 : Nat := 118140960795 + 3201714 * 2 ^ 59
def prefixEnd_3201714 : Nat := 4983230072969 + 3 ^ 40 * 3201714 * 2
def baseEnd_3201714 : Nat := 1644018200229391512950591

theorem tailTrace_3201714 : CollatzResearch.WordTrace tailWord_3201714 prefixEnd_3201714 1644018200229391512950591 := by
  unfold tailWord_3201714
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194025780686115515651049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77850735415162974708402797 29194025780686115515651049)
  ·
    refine ⟨21895519335514586636738287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29194025780686115515651049 21895519335514586636738287)
    ·
      refine ⟨32843279003271879955107431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21895519335514586636738287 32843279003271879955107431)
      ·
        refine ⟨49264918504907819932661147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32843279003271879955107431 49264918504907819932661147)
        ·
          refine ⟨73897377757361729898991721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49264918504907819932661147 73897377757361729898991721)
          ·
            refine ⟨55423033318021297424243791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73897377757361729898991721 55423033318021297424243791)
            ·
              refine ⟨83134549977031946136365687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55423033318021297424243791 83134549977031946136365687)
              ·
                refine ⟨124701824965547919204548531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83134549977031946136365687 124701824965547919204548531)
                ·
                  refine ⟨187052737448321878806822797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124701824965547919204548531 187052737448321878806822797)
                  ·
                    refine ⟨70144776543120704552558549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187052737448321878806822797 70144776543120704552558549)
                    ·
                      refine ⟨1644018200229391512950591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70144776543120704552558549 1644018200229391512950591)
                      ·
                        rfl

theorem cell23_3201714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_3201714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201714 prefixEnd_3201714 := by exact prefixLift 3201714
  have htrace : WordTrace (prefixWord ++ tailWord_3201714) baseStart_3201714 baseEnd_3201714 := by
    simpa [prefixWord, tailWord_3201714, baseEnd_3201714] using wordTrace_append hprefix tailTrace_3201714
  have hstable : (prefixWord ++ tailWord_3201714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201714).length < 2 ^ (prefixWord ++ tailWord_3201714).sum := by decide
  have hdescent : baseEnd_3201714 < baseStart_3201714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201721 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_3201721 : Nat := 118140960795 + 3201721 * 2 ^ 59
def prefixEnd_3201721 : Nat := 4983230072969 + 3 ^ 40 * 3201721 * 2
def baseEnd_3201721 : Nat := 548007264864657661854353

theorem tailTrace_3201721 : CollatzResearch.WordTrace tailWord_3201721 prefixEnd_3201721 548007264864657661854353 := by
  unfold tailWord_3201721
  simp only [CollatzResearch.WordTrace]
  refine ⟨116776358433719102258109017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77850905622479401505406011 116776358433719102258109017)
  ·
    refine ⟨87582268825289326693581763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116776358433719102258109017 87582268825289326693581763)
    ·
      refine ⟨131373403237933990040372645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87582268825289326693581763 131373403237933990040372645)
      ·
        refine ⟨24632513107112623132569871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131373403237933990040372645 24632513107112623132569871)
        ·
          refine ⟨36948769660668934698854807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24632513107112623132569871 36948769660668934698854807)
          ·
            refine ⟨55423154491003402048282211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36948769660668934698854807 55423154491003402048282211)
            ·
              refine ⟨83134731736505103072423317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55423154491003402048282211 83134731736505103072423317)
              ·
                refine ⟨3896940550148676706519843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83134731736505103072423317 3896940550148676706519843)
                ·
                  refine ⟨5845410825223015059779765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896940550148676706519843 5845410825223015059779765)
                  ·
                    refine ⟨548007264864657661854353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5845410825223015059779765 548007264864657661854353)
                    ·
                      rfl

theorem cell23_3201721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_3201721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201721 prefixEnd_3201721 := by exact prefixLift 3201721
  have htrace : WordTrace (prefixWord ++ tailWord_3201721) baseStart_3201721 baseEnd_3201721 := by
    simpa [prefixWord, tailWord_3201721, baseEnd_3201721] using wordTrace_append hprefix tailTrace_3201721
  have hstable : (prefixWord ++ tailWord_3201721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201721).length < 2 ^ (prefixWord ++ tailWord_3201721).sum := by decide
  have hdescent : baseEnd_3201721 < baseStart_3201721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201728 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2]
def baseStart_3201728 : Nat := 118140960795 + 3201728 * 2 ^ 59
def prefixEnd_3201728 : Nat := 4983230072969 + 3 ^ 40 * 3201728 * 2
def baseEnd_3201728 : Nat := 1644025388958554458175527

theorem tailTrace_3201728 : CollatzResearch.WordTrace tailWord_3201728 prefixEnd_3201728 1644025388958554458175527 := by
  unfold tailWord_3201728
  simp only [CollatzResearch.WordTrace]
  refine ⟨58388306872346871226806919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77851075829795828302409225 58388306872346871226806919)
  ·
    refine ⟨87582460308520306840210379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58388306872346871226806919 87582460308520306840210379)
    ·
      refine ⟨131373690462780460260315569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87582460308520306840210379 131373690462780460260315569)
      ·
        refine ⟨98530267847085345195236677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131373690462780460260315569 98530267847085345195236677)
        ·
          refine ⟨18474425221328502224106877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98530267847085345195236677 18474425221328502224106877)
          ·
            refine ⟨6927909457998188334040079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18474425221328502224106877 6927909457998188334040079)
            ·
              refine ⟨10391864186997282501060119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927909457998188334040079 10391864186997282501060119)
              ·
                refine ⟨15587796280495923751590179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10391864186997282501060119 15587796280495923751590179)
                ·
                  refine ⟨23381694420743885627385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15587796280495923751590179 23381694420743885627385269)
                  ·
                    refine ⟨2192033851944739277567369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23381694420743885627385269 2192033851944739277567369)
                    ·
                      refine ⟨1644025388958554458175527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192033851944739277567369 1644025388958554458175527)
                      ·
                        rfl

theorem cell23_3201728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_3201728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201728 prefixEnd_3201728 := by exact prefixLift 3201728
  have htrace : WordTrace (prefixWord ++ tailWord_3201728) baseStart_3201728 baseEnd_3201728 := by
    simpa [prefixWord, tailWord_3201728, baseEnd_3201728] using wordTrace_append hprefix tailTrace_3201728
  have hstable : (prefixWord ++ tailWord_3201728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201728).length < 2 ^ (prefixWord ++ tailWord_3201728).sum := by decide
  have hdescent : baseEnd_3201728 < baseStart_3201728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201729 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3201729 : Nat := 118140960795 + 3201729 * 2 ^ 59
def prefixEnd_3201729 : Nat := 4983230072969 + 3 ^ 40 * 3201729 * 2
def baseEnd_3201729 : Nat := 548008634146402984754341

theorem tailTrace_3201729 : CollatzResearch.WordTrace tailWord_3201729 prefixEnd_3201729 548008634146402984754341 := by
  unfold tailWord_3201729
  simp only [CollatzResearch.WordTrace]
  refine ⟨116776650217690119624400241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77851100145126746416266827 116776650217690119624400241)
  ·
    refine ⟨87582487663267589718300181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116776650217690119624400241 87582487663267589718300181)
    ·
      refine ⟨4105429109215668268045321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87582487663267589718300181 4105429109215668268045321)
      ·
        refine ⟨3079071831911751201033991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4105429109215668268045321 3079071831911751201033991)
        ·
          refine ⟨4618607747867626801550987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079071831911751201033991 4618607747867626801550987)
          ·
            refine ⟨6927911621801440202326481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618607747867626801550987 6927911621801440202326481)
            ·
              refine ⟨5195933716351080151744861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927911621801440202326481 5195933716351080151744861)
              ·
                refine ⟨1948475143631655056904323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5195933716351080151744861 1948475143631655056904323)
                ·
                  refine ⟨2922712715447482585356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948475143631655056904323 2922712715447482585356485)
                  ·
                    refine ⟨548008634146402984754341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922712715447482585356485 548008634146402984754341)
                    ·
                      rfl

theorem cell23_3201729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3201729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201729 prefixEnd_3201729 := by exact prefixLift 3201729
  have htrace : WordTrace (prefixWord ++ tailWord_3201729) baseStart_3201729 baseEnd_3201729 := by
    simpa [prefixWord, tailWord_3201729, baseEnd_3201729] using wordTrace_append hprefix tailTrace_3201729
  have hstable : (prefixWord ++ tailWord_3201729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201729).length < 2 ^ (prefixWord ++ tailWord_3201729).sum := by decide
  have hdescent : baseEnd_3201729 < baseStart_3201729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201738 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3201738 : Nat := 118140960795 + 3201738 * 2 ^ 59
def prefixEnd_3201738 : Nat := 4983230072969 + 3 ^ 40 * 3201738 * 2
def baseEnd_3201738 : Nat := 548010174588366473016827

theorem tailTrace_3201738 : CollatzResearch.WordTrace tailWord_3201738 prefixEnd_3201738 548010174588366473016827 := by
  unfold tailWord_3201738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194244618664378540369467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77851318983105009440985245 29194244618664378540369467)
  ·
    refine ⟨43791366927996567810554201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29194244618664378540369467 43791366927996567810554201)
    ·
      refine ⟨32843525195997425857915651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43791366927996567810554201 32843525195997425857915651)
      ·
        refine ⟨49265287793996138786873477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32843525195997425857915651 49265287793996138786873477)
        ·
          refine ⟨9237241461374276022538777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49265287793996138786873477 9237241461374276022538777)
          ·
            refine ⟨6927931096030707016904083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9237241461374276022538777 6927931096030707016904083)
            ·
              refine ⟨10391896644046060525356125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927931096030707016904083 10391896644046060525356125)
              ·
                refine ⟨3896961241517272697008547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10391896644046060525356125 3896961241517272697008547)
                ·
                  refine ⟨5845441862275909045512821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3896961241517272697008547 5845441862275909045512821)
                  ·
                    refine ⟨548010174588366473016827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5845441862275909045512821 548010174588366473016827)
                    ·
                      rfl

theorem cell23_3201738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3201738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201738 prefixEnd_3201738 := by exact prefixLift 3201738
  have htrace : WordTrace (prefixWord ++ tailWord_3201738) baseStart_3201738 baseEnd_3201738 := by
    simpa [prefixWord, tailWord_3201738, baseEnd_3201738] using wordTrace_append hprefix tailTrace_3201738
  have hstable : (prefixWord ++ tailWord_3201738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201738).length < 2 ^ (prefixWord ++ tailWord_3201738).sum := by decide
  have hdescent : baseEnd_3201738 < baseStart_3201738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201761 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3201761 : Nat := 118140960795 + 3201761 * 2 ^ 59
def prefixEnd_3201761 : Nat := 4983230072969 + 3 ^ 40 * 3201761 * 2
def baseEnd_3201761 : Nat := 1644042333820152829062875

theorem tailTrace_3201761 : CollatzResearch.WordTrace tailWord_3201761 prefixEnd_3201761 1644042333820152829062875 := by
  unfold tailWord_3201761
  simp only [CollatzResearch.WordTrace]
  refine ⟨116777817353574189089565137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77851878235716126059710091 116777817353574189089565137)
  ·
    refine ⟨87583363015180641817173853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116777817353574189089565137 87583363015180641817173853)
    ·
      refine ⟨32843761130692740681440195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87583363015180641817173853 32843761130692740681440195)
      ·
        refine ⟨49265641696039111022160293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32843761130692740681440195 49265641696039111022160293)
        ·
          refine ⟨9237307818007333316655055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49265641696039111022160293 9237307818007333316655055)
          ·
            refine ⟨13855961727010999974982583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237307818007333316655055 13855961727010999974982583)
            ·
              refine ⟨20783942590516499962473875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13855961727010999974982583 20783942590516499962473875)
              ·
                refine ⟨31175913885774749943710813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20783942590516499962473875 31175913885774749943710813)
                ·
                  refine ⟨11690967707165531228891555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31175913885774749943710813 11690967707165531228891555)
                  ·
                    refine ⟨17536451560748296843337333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11690967707165531228891555 17536451560748296843337333)
                    ·
                      refine ⟨1644042333820152829062875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17536451560748296843337333 1644042333820152829062875)
                      ·
                        rfl

theorem cell23_3201761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3201761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201761 prefixEnd_3201761 := by exact prefixLift 3201761
  have htrace : WordTrace (prefixWord ++ tailWord_3201761) baseStart_3201761 baseEnd_3201761 := by
    simpa [prefixWord, tailWord_3201761, baseEnd_3201761] using wordTrace_append hprefix tailTrace_3201761
  have hstable : (prefixWord ++ tailWord_3201761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201761).length < 2 ^ (prefixWord ++ tailWord_3201761).sum := by decide
  have hdescent : baseEnd_3201761 < baseStart_3201761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201775 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 3, 2, 2]
def baseStart_3201775 : Nat := 118140960795 + 3201775 * 2 ^ 59
def prefixEnd_3201775 : Nat := 4983230072969 + 3 ^ 40 * 3201775 * 2
def baseEnd_3201775 : Nat := 1644049522549315774287811

theorem tailTrace_3201775 : CollatzResearch.WordTrace tailWord_3201775 prefixEnd_3201775 1644049522549315774287811 := by
  unfold tailWord_3201775
  simp only [CollatzResearch.WordTrace]
  refine ⟨116778327975523469480574779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77852218650348979653716519 116778327975523469480574779)
  ·
    refine ⟨175167491963285204220862169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116778327975523469480574779 175167491963285204220862169)
    ·
      refine ⟨131375618972463903165646627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175167491963285204220862169 131375618972463903165646627)
      ·
        refine ⟨197063428458695854748469941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131375618972463903165646627 197063428458695854748469941)
        ·
          refine ⟨18474696418002736382669057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197063428458695854748469941 18474696418002736382669057)
          ·
            refine ⟨13856022313502052287001793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18474696418002736382669057 13856022313502052287001793)
            ·
              refine ⟨10392016735126539215251345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13856022313502052287001793 10392016735126539215251345)
              ·
                refine ⟨7794012551344904411438509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10392016735126539215251345 7794012551344904411438509)
                ·
                  refine ⟨2922754706754339154289441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7794012551344904411438509 2922754706754339154289441)
                  ·
                    refine ⟨2192066030065754365717081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922754706754339154289441 2192066030065754365717081)
                    ·
                      refine ⟨1644049522549315774287811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192066030065754365717081 1644049522549315774287811)
                      ·
                        rfl

theorem cell23_3201775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 2, 2].length) (baseStart_3201775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201775 prefixEnd_3201775 := by exact prefixLift 3201775
  have htrace : WordTrace (prefixWord ++ tailWord_3201775) baseStart_3201775 baseEnd_3201775 := by
    simpa [prefixWord, tailWord_3201775, baseEnd_3201775] using wordTrace_append hprefix tailTrace_3201775
  have hstable : (prefixWord ++ tailWord_3201775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201775).length < 2 ^ (prefixWord ++ tailWord_3201775).sum := by decide
  have hdescent : baseEnd_3201775 < baseStart_3201775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201791 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_3201791 : Nat := 118140960795 + 3201791 * 2 ^ 59
def prefixEnd_3201791 : Nat := 4983230072969 + 3 ^ 40 * 3201791 * 2
def baseEnd_3201791 : Nat := 1644057738239787711687737

theorem tailTrace_3201791 : CollatzResearch.WordTrace tailWord_3201791 prefixEnd_3201791 1644057738239787711687737 := by
  unfold tailWord_3201791
  simp only [CollatzResearch.WordTrace]
  refine ⟨116778911543465504213157227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77852607695643669475438151 116778911543465504213157227)
  ·
    refine ⟨175168367315198256319735841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116778911543465504213157227 175168367315198256319735841)
    ·
      refine ⟨131376275486398692239801881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175168367315198256319735841 131376275486398692239801881)
      ·
        refine ⟨98532206614799019179851411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131376275486398692239801881 98532206614799019179851411)
        ·
          refine ⟨147798309922198528769777117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98532206614799019179851411 147798309922198528769777117)
          ·
            refine ⟨55424366220824448288666419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147798309922198528769777117 55424366220824448288666419)
            ·
              refine ⟨83136549331236672432999629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55424366220824448288666419 83136549331236672432999629)
              ·
                refine ⟨31176205999213752162374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83136549331236672432999629 31176205999213752162374861)
                ·
                  refine ⟨11691077249705157060890573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31176205999213752162374861 11691077249705157060890573)
                  ·
                    refine ⟨4384153968639433897833965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11691077249705157060890573 4384153968639433897833965)
                    ·
                      refine ⟨1644057738239787711687737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4384153968639433897833965 1644057738239787711687737)
                      ·
                        rfl

theorem cell23_3201791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_3201791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201791 prefixEnd_3201791 := by exact prefixLift 3201791
  have htrace : WordTrace (prefixWord ++ tailWord_3201791) baseStart_3201791 baseEnd_3201791 := by
    simpa [prefixWord, tailWord_3201791, baseEnd_3201791] using wordTrace_append hprefix tailTrace_3201791
  have hstable : (prefixWord ++ tailWord_3201791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201791).length < 2 ^ (prefixWord ++ tailWord_3201791).sum := by decide
  have hdescent : baseEnd_3201791 < baseStart_3201791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201825 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3201825 : Nat := 118140960795 + 3201825 * 2 ^ 59
def prefixEnd_3201825 : Nat := 4983230072969 + 3 ^ 40 * 3201825 * 2
def baseEnd_3201825 : Nat := 1644075196582040578662581

theorem tailTrace_3201825 : CollatzResearch.WordTrace tailWord_3201825 prefixEnd_3201825 1644075196582040578662581 := by
  unfold tailWord_3201825
  simp only [CollatzResearch.WordTrace]
  refine ⟨116780151625342328019894929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77853434416894885346596619 116780151625342328019894929)
  ·
    refine ⟨87585113719006746014921197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116780151625342328019894929 87585113719006746014921197)
    ·
      refine ⟨32844417644627529755595449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87585113719006746014921197 32844417644627529755595449)
      ·
        refine ⟨24633313233470647316696587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32844417644627529755595449 24633313233470647316696587)
        ·
          refine ⟨36949969850205970975044881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24633313233470647316696587 36949969850205970975044881)
          ·
            refine ⟨27712477387654478231283661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36949969850205970975044881 27712477387654478231283661)
            ·
              refine ⟨10392179020370429336731373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27712477387654478231283661 10392179020370429336731373)
              ·
                refine ⟨3897067132638911001274265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10392179020370429336731373 3897067132638911001274265)
                ·
                  refine ⟨2922800349479183250955699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897067132638911001274265 2922800349479183250955699)
                  ·
                    refine ⟨4384200524218774876433549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2922800349479183250955699 4384200524218774876433549)
                    ·
                      refine ⟨1644075196582040578662581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4384200524218774876433549 1644075196582040578662581)
                      ·
                        rfl

theorem cell23_3201825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3201825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201825 prefixEnd_3201825 := by exact prefixLift 3201825
  have htrace : WordTrace (prefixWord ++ tailWord_3201825) baseStart_3201825 baseEnd_3201825 := by
    simpa [prefixWord, tailWord_3201825, baseEnd_3201825] using wordTrace_append hprefix tailTrace_3201825
  have hstable : (prefixWord ++ tailWord_3201825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201825).length < 2 ^ (prefixWord ++ tailWord_3201825).sum := by decide
  have hdescent : baseEnd_3201825 < baseStart_3201825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201860 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3201860 : Nat := 118140960795 + 3201860 * 2 ^ 59
def prefixEnd_3201860 : Nat := 4983230072969 + 3 ^ 40 * 3201860 * 2
def baseEnd_3201860 : Nat := 1644093168404947941724921

theorem tailTrace_3201860 : CollatzResearch.WordTrace tailWord_3201860 prefixEnd_3201860 1644093168404947941724921 := by
  unfold tailWord_3201860
  simp only [CollatzResearch.WordTrace]
  refine ⟨58390714090107764498709517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77854285453477019331612689 58390714090107764498709517)
  ·
    refine ⟨21896517783790411687016069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58390714090107764498709517 21896517783790411687016069)
    ·
      refine ⟨4105597084460702191315513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21896517783790411687016069 4105597084460702191315513)
      ·
        refine ⟨3079197813345526643486635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4105597084460702191315513 3079197813345526643486635)
        ·
          refine ⟨4618796720018289965229953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079197813345526643486635 4618796720018289965229953)
          ·
            refine ⟨3464097540013717473922465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618796720018289965229953 3464097540013717473922465)
            ·
              refine ⟨2598073155010288105441849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464097540013717473922465 2598073155010288105441849)
              ·
                refine ⟨1948554866257716079081387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598073155010288105441849 1948554866257716079081387)
                ·
                  refine ⟨2922832299386574118622081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948554866257716079081387 2922832299386574118622081)
                  ·
                    refine ⟨2192124224539930588966561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922832299386574118622081 2192124224539930588966561)
                    ·
                      refine ⟨1644093168404947941724921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192124224539930588966561 1644093168404947941724921)
                      ·
                        rfl

theorem cell23_3201860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3201860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201860 prefixEnd_3201860 := by exact prefixLift 3201860
  have htrace : WordTrace (prefixWord ++ tailWord_3201860) baseStart_3201860 baseEnd_3201860 := by
    simpa [prefixWord, tailWord_3201860, baseEnd_3201860] using wordTrace_append hprefix tailTrace_3201860
  have hstable : (prefixWord ++ tailWord_3201860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201860).length < 2 ^ (prefixWord ++ tailWord_3201860).sum := by decide
  have hdescent : baseEnd_3201860 < baseStart_3201860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201868 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3201868 : Nat := 118140960795 + 3201868 * 2 ^ 59
def prefixEnd_3201868 : Nat := 4983230072969 + 3 ^ 40 * 3201868 * 2
def baseEnd_3201868 : Nat := 1644097276250183910424883

theorem tailTrace_3201868 : CollatzResearch.WordTrace tailWord_3201868 prefixEnd_3201868 1644097276250183910424883 := by
  unfold tailWord_3201868
  simp only [CollatzResearch.WordTrace]
  refine ⟨58390859982093273181855129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77854479976124364242473505 58390859982093273181855129)
  ·
    refine ⟨43793144986569954886391347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58390859982093273181855129 43793144986569954886391347)
    ·
      refine ⟨65689717479854932329587021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43793144986569954886391347 65689717479854932329587021)
      ·
        refine ⟨24633644054945599623595133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65689717479854932329587021 24633644054945599623595133)
        ·
          refine ⟨9237616520604599858848175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24633644054945599623595133 9237616520604599858848175)
          ·
            refine ⟨13856424780906899788272263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237616520604599858848175 13856424780906899788272263)
            ·
              refine ⟨20784637171360349682408395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13856424780906899788272263 20784637171360349682408395)
              ·
                refine ⟨31176955757040524523612593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20784637171360349682408395 31176955757040524523612593)
                ·
                  refine ⟨23382716817780393392709445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31176955757040524523612593 23382716817780393392709445)
                  ·
                    refine ⟨4384259403333823761133021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23382716817780393392709445 4384259403333823761133021)
                    ·
                      refine ⟨1644097276250183910424883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4384259403333823761133021 1644097276250183910424883)
                      ·
                        rfl

theorem cell23_3201868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3201868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201868 prefixEnd_3201868 := by exact prefixLift 3201868
  have htrace : WordTrace (prefixWord ++ tailWord_3201868) baseStart_3201868 baseEnd_3201868 := by
    simpa [prefixWord, tailWord_3201868, baseEnd_3201868] using wordTrace_append hprefix tailTrace_3201868
  have hstable : (prefixWord ++ tailWord_3201868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201868).length < 2 ^ (prefixWord ++ tailWord_3201868).sum := by decide
  have hdescent : baseEnd_3201868 < baseStart_3201868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201882 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2]
def baseStart_3201882 : Nat := 118140960795 + 3201882 * 2 ^ 59
def prefixEnd_3201882 : Nat := 4983230072969 + 3 ^ 40 * 3201882 * 2
def baseEnd_3201882 : Nat := 1644104464979346855649819

theorem tailTrace_3201882 : CollatzResearch.WordTrace tailWord_3201882 prefixEnd_3201882 1644104464979346855649819 := by
  unfold tailWord_3201882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29195557646533956688679975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77854820390757217836479933 29195557646533956688679975)
  ·
    refine ⟨43793336469800935033019963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29195557646533956688679975 43793336469800935033019963)
    ·
      refine ⟨65690004704701402549529945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43793336469800935033019963 65690004704701402549529945)
      ·
        refine ⟨49267503528526051912147459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65690004704701402549529945 49267503528526051912147459)
        ·
          refine ⟨73901255292789077868221189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49267503528526051912147459 73901255292789077868221189)
          ·
            refine ⟨13856485367397952100291473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73901255292789077868221189 13856485367397952100291473)
            ·
              refine ⟨10392364025548464075218605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13856485367397952100291473 10392364025548464075218605)
              ·
                refine ⟨3897136509580674028206977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10392364025548464075218605 3897136509580674028206977)
                ·
                  refine ⟨2922852382185505521155233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897136509580674028206977 2922852382185505521155233)
                  ·
                    refine ⟨2192139286639129140866425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2922852382185505521155233 2192139286639129140866425)
                    ·
                      refine ⟨1644104464979346855649819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192139286639129140866425 1644104464979346855649819)
                      ·
                        rfl

theorem cell23_3201882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_3201882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201882 prefixEnd_3201882 := by exact prefixLift 3201882
  have htrace : WordTrace (prefixWord ++ tailWord_3201882) baseStart_3201882 baseEnd_3201882 := by
    simpa [prefixWord, tailWord_3201882, baseEnd_3201882] using wordTrace_append hprefix tailTrace_3201882
  have hstable : (prefixWord ++ tailWord_3201882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201882).length < 2 ^ (prefixWord ++ tailWord_3201882).sum := by decide
  have hdescent : baseEnd_3201882 < baseStart_3201882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201905 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 5]
def baseStart_3201905 : Nat := 118140960795 + 3201905 * 2 ^ 59
def prefixEnd_3201905 : Nat := 4983230072969 + 3 ^ 40 * 3201905 * 2
def baseEnd_3201905 : Nat := 182679586114933362851357

theorem tailTrace_3201905 : CollatzResearch.WordTrace tailWord_3201905 prefixEnd_3201905 182679586114933362851357 := by
  unfold tailWord_3201905
  simp only [CollatzResearch.WordTrace]
  refine ⟨116783069465052501682807169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77855379643368334455204779 116783069465052501682807169)
  ·
    refine ⟨87587302098789376262105377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116783069465052501682807169 87587302098789376262105377)
    ·
      refine ⟨65690476574092032196579033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87587302098789376262105377 65690476574092032196579033)
      ·
        refine ⟨49267857430569024147434275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65690476574092032196579033 49267857430569024147434275)
        ·
          refine ⟨73901786145853536221151413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49267857430569024147434275 73901786145853536221151413)
          ·
            refine ⟨6928292451173769020732945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73901786145853536221151413 6928292451173769020732945)
            ·
              refine ⟨5196219338380326765549709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6928292451173769020732945 5196219338380326765549709)
              ·
                refine ⟨1948582251892622537081141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5196219338380326765549709 1948582251892622537081141)
                ·
                  refine ⟨182679586114933362851357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1948582251892622537081141 182679586114933362851357)
                  ·
                    rfl

theorem cell23_3201905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 5].length) (baseStart_3201905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201905 prefixEnd_3201905 := by exact prefixLift 3201905
  have htrace : WordTrace (prefixWord ++ tailWord_3201905) baseStart_3201905 baseEnd_3201905 := by
    simpa [prefixWord, tailWord_3201905, baseEnd_3201905] using wordTrace_append hprefix tailTrace_3201905
  have hstable : (prefixWord ++ tailWord_3201905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201905).length < 2 ^ (prefixWord ++ tailWord_3201905).sum := by decide
  have hdescent : baseEnd_3201905 < baseStart_3201905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201911 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3201911 : Nat := 118140960795 + 3201911 * 2 ^ 59
def prefixEnd_3201911 : Nat := 4983230072969 + 3 ^ 40 * 3201911 * 2
def baseEnd_3201911 : Nat := 1644119355918327242187185

theorem tailTrace_3201911 : CollatzResearch.WordTrace tailWord_3201911 prefixEnd_3201911 1644119355918327242187185 := by
  unfold tailWord_3201911
  simp only [CollatzResearch.WordTrace]
  refine ⟨116783288303030764707525587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77855525535353843138350391 116783288303030764707525587)
  ·
    refine ⟨175174932454546147061288381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116783288303030764707525587 175174932454546147061288381)
    ·
      refine ⟨65690599670454805147983143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175174932454546147061288381 65690599670454805147983143)
      ·
        refine ⟨98535899505682207721974715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65690599670454805147983143 98535899505682207721974715)
        ·
          refine ⟨147803849258523311582962073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98535899505682207721974715 147803849258523311582962073)
          ·
            refine ⟨110852886943892483687221555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147803849258523311582962073 110852886943892483687221555)
            ·
              refine ⟨166279330415838725530832333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110852886943892483687221555 166279330415838725530832333)
              ·
                refine ⟨62354748905939522074062125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166279330415838725530832333 62354748905939522074062125)
                ·
                  refine ⟨23383030839727320777773297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62354748905939522074062125 23383030839727320777773297)
                  ·
                    refine ⟨17537273129795490583329973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23383030839727320777773297 17537273129795490583329973)
                    ·
                      refine ⟨1644119355918327242187185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17537273129795490583329973 1644119355918327242187185)
                      ·
                        rfl

theorem cell23_3201911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3201911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201911 prefixEnd_3201911 := by exact prefixLift 3201911
  have htrace : WordTrace (prefixWord ++ tailWord_3201911) baseStart_3201911 baseEnd_3201911 := by
    simpa [prefixWord, tailWord_3201911, baseEnd_3201911] using wordTrace_append hprefix tailTrace_3201911
  have hstable : (prefixWord ++ tailWord_3201911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201911).length < 2 ^ (prefixWord ++ tailWord_3201911).sum := by decide
  have hdescent : baseEnd_3201911 < baseStart_3201911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201961 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 10]
def baseStart_3201961 : Nat := 118140960795 + 3201961 * 2 ^ 59
def prefixEnd_3201961 : Nat := 4983230072969 + 3 ^ 40 * 3201961 * 2
def baseEnd_3201961 : Nat := 182682781105672449617995

theorem tailTrace_3201961 : CollatzResearch.WordTrace tailWord_3201961 prefixEnd_3201961 182682781105672449617995 := by
  unfold tailWord_3201961
  simp only [CollatzResearch.WordTrace]
  refine ⟨116785111952849623246845737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77856741301899748831230491 116785111952849623246845737)
  ·
    refine ⟨87588833964637217435134303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116785111952849623246845737 87588833964637217435134303)
    ·
      refine ⟨131383250946955826152701455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87588833964637217435134303 131383250946955826152701455)
      ·
        refine ⟨197074876420433739229052183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131383250946955826152701455 197074876420433739229052183)
        ·
          refine ⟨295612314630650608843578275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197074876420433739229052183 295612314630650608843578275)
          ·
            refine ⟨443418471945975913265367413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295612314630650608843578275 443418471945975913265367413)
            ·
              refine ⟨41570481744935241868628195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443418471945975913265367413 41570481744935241868628195)
              ·
                refine ⟨62355722617402862802942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41570481744935241868628195 62355722617402862802942293)
                ·
                  refine ⟨182682781105672449617995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 62355722617402862802942293 182682781105672449617995)
                  ·
                    rfl

theorem cell23_3201961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_3201961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201961 prefixEnd_3201961 := by exact prefixLift 3201961
  have htrace : WordTrace (prefixWord ++ tailWord_3201961) baseStart_3201961 baseEnd_3201961 := by
    simpa [prefixWord, tailWord_3201961, baseEnd_3201961] using wordTrace_append hprefix tailTrace_3201961
  have hstable : (prefixWord ++ tailWord_3201961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201961).length < 2 ^ (prefixWord ++ tailWord_3201961).sum := by decide
  have hdescent : baseEnd_3201961 < baseStart_3201961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201972 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3201972 : Nat := 118140960795 + 3201972 * 2 ^ 59
def prefixEnd_3201972 : Nat := 4983230072969 + 3 ^ 40 * 3201972 * 2
def baseEnd_3201972 : Nat := 1644150678238251503524405

theorem tailTrace_3201972 : CollatzResearch.WordTrace tailWord_3201972 prefixEnd_3201972 1644150678238251503524405 := by
  unfold tailWord_3201972
  simp only [CollatzResearch.WordTrace]
  refine ⟨58392756577904886062748085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77857008770539848083664113 58392756577904886062748085)
  ·
    refine ⟨5474320929178583068382633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58392756577904886062748085 5474320929178583068382633)
    ·
      refine ⟨4105740696883937301286975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5474320929178583068382633 4105740696883937301286975)
      ·
        refine ⟨6158611045325905951930463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105740696883937301286975 6158611045325905951930463)
        ·
          refine ⟨9237916567988858927895695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158611045325905951930463 9237916567988858927895695)
          ·
            refine ⟨13856874851983288391843543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237916567988858927895695 13856874851983288391843543)
            ·
              refine ⟨20785312277974932587765315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13856874851983288391843543 20785312277974932587765315)
              ·
                refine ⟨31177968416962398881647973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20785312277974932587765315 31177968416962398881647973)
                ·
                  refine ⟨5845869078180449790308995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31177968416962398881647973 5845869078180449790308995)
                  ·
                    refine ⟨8768803617270674685463493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5845869078180449790308995 8768803617270674685463493)
                    ·
                      refine ⟨1644150678238251503524405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8768803617270674685463493 1644150678238251503524405)
                      ·
                        rfl

theorem cell23_3201972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3201972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201972 prefixEnd_3201972 := by exact prefixLift 3201972
  have htrace : WordTrace (prefixWord ++ tailWord_3201972) baseStart_3201972 baseEnd_3201972 := by
    simpa [prefixWord, tailWord_3201972, baseEnd_3201972] using wordTrace_append hprefix tailTrace_3201972
  have hstable : (prefixWord ++ tailWord_3201972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201972).length < 2 ^ (prefixWord ++ tailWord_3201972).sum := by decide
  have hdescent : baseEnd_3201972 < baseStart_3201972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201978 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 6]
def baseStart_3201978 : Nat := 118140960795 + 3201978 * 2 ^ 59
def prefixEnd_3201978 : Nat := 4983230072969 + 3 ^ 40 * 3201978 * 2
def baseEnd_3201978 : Nat := 182683751013575386672153

theorem tailTrace_3201978 : CollatzResearch.WordTrace tailWord_3201978 prefixEnd_3201978 182683751013575386672153 := by
  unfold tailWord_3201978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29196432998447008787553647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77857154662525356766809725 29196432998447008787553647)
  ·
    refine ⟨43794649497670513181330471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29196432998447008787553647 43794649497670513181330471)
    ·
      refine ⟨65691974246505769771995707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43794649497670513181330471 65691974246505769771995707)
      ·
        refine ⟨98537961369758654657993561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65691974246505769771995707 98537961369758654657993561)
        ·
          refine ⟨73903471027318990993495171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98537961369758654657993561 73903471027318990993495171)
          ·
            refine ⟨110855206540978486490242757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73903471027318990993495171 110855206540978486490242757)
            ·
              refine ⟨20785351226433466216920517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110855206540978486490242757 20785351226433466216920517)
              ·
                refine ⟨3897253354956274915672597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20785351226433466216920517 3897253354956274915672597)
                ·
                  refine ⟨182683751013575386672153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3897253354956274915672597 182683751013575386672153)
                  ·
                    rfl

theorem cell23_3201978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_3201978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201978 prefixEnd_3201978 := by exact prefixLift 3201978
  have htrace : WordTrace (prefixWord ++ tailWord_3201978) baseStart_3201978 baseEnd_3201978 := by
    simpa [prefixWord, tailWord_3201978, baseEnd_3201978] using wordTrace_append hprefix tailTrace_3201978
  have hstable : (prefixWord ++ tailWord_3201978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201978).length < 2 ^ (prefixWord ++ tailWord_3201978).sum := by decide
  have hdescent : baseEnd_3201978 < baseStart_3201978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201995 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 6]
def baseStart_3201995 : Nat := 118140960795 + 3201995 * 2 ^ 59
def prefixEnd_3201995 : Nat := 4983230072969 + 3 ^ 40 * 3201995 * 2
def baseEnd_3201995 : Nat := 182684720921478323726311

theorem tailTrace_3201995 : CollatzResearch.WordTrace tailWord_3201995 prefixEnd_3201995 182684720921478323726311 := by
  unfold tailWord_3201995
  simp only [CollatzResearch.WordTrace]
  refine ⟨116786352034726447053583439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77857568023150964702388959 116786352034726447053583439)
  ·
    refine ⟨175179528052089670580375159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116786352034726447053583439 175179528052089670580375159)
    ·
      refine ⟨262769292078134505870562739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175179528052089670580375159 262769292078134505870562739)
      ·
        refine ⟨394153938117201758805844109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262769292078134505870562739 394153938117201758805844109)
        ·
          refine ⟨147807726793950659552191541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 394153938117201758805844109 147807726793950659552191541)
          ·
            refine ⟨13856974386932874333017957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147807726793950659552191541 13856974386932874333017957)
            ·
              refine ⟨2598182697549913937440867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13856974386932874333017957 2598182697549913937440867)
              ·
                refine ⟨3897274046324870906161301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598182697549913937440867 3897274046324870906161301)
                ·
                  refine ⟨182684720921478323726311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3897274046324870906161301 182684720921478323726311)
                  ·
                    rfl

theorem cell23_3201995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 6].length) (baseStart_3201995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3201995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3201995 prefixEnd_3201995 := by exact prefixLift 3201995
  have htrace : WordTrace (prefixWord ++ tailWord_3201995) baseStart_3201995 baseEnd_3201995 := by
    simpa [prefixWord, tailWord_3201995, baseEnd_3201995] using wordTrace_append hprefix tailTrace_3201995
  have hstable : (prefixWord ++ tailWord_3201995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201995).length < 2 ^ (prefixWord ++ tailWord_3201995).sum := by decide
  have hdescent : baseEnd_3201995 < baseStart_3201995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202045 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_3202045 : Nat := 118140960795 + 3202045 * 2 ^ 59
def prefixEnd_3202045 : Nat := 4983230072969 + 3 ^ 40 * 3202045 * 2
def baseEnd_3202045 : Nat := 1644188162326029717911569

theorem tailTrace_3202045 : CollatzResearch.WordTrace tailWord_3202045 prefixEnd_3202045 1644188162326029717911569 := by
  unfold tailWord_3202045
  simp only [CollatzResearch.WordTrace]
  refine ⟨116788175684545305592903589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77858783789696870395269059 116788175684545305592903589)
  ·
    refine ⟨21897782940852244798669423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116788175684545305592903589 21897782940852244798669423)
    ·
      refine ⟨32846674411278367198004135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21897782940852244798669423 32846674411278367198004135)
      ·
        refine ⟨49270011616917550797006203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32846674411278367198004135 49270011616917550797006203)
        ·
          refine ⟨73905017425376326195509305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49270011616917550797006203 73905017425376326195509305)
          ·
            refine ⟨55428763069032244646631979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73905017425376326195509305 55428763069032244646631979)
            ·
              refine ⟨83143144603548366969947969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55428763069032244646631979 83143144603548366969947969)
              ·
                refine ⟨62357358452661275227460977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83143144603548366969947969 62357358452661275227460977)
                ·
                  refine ⟨46768018839495956420595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62357358452661275227460977 46768018839495956420595733)
                  ·
                    refine ⟨2192250883101372957215425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46768018839495956420595733 2192250883101372957215425)
                    ·
                      refine ⟨1644188162326029717911569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192250883101372957215425 1644188162326029717911569)
                      ·
                        rfl

theorem cell23_3202045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_3202045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202045 prefixEnd_3202045 := by exact prefixLift 3202045
  have htrace : WordTrace (prefixWord ++ tailWord_3202045) baseStart_3202045 baseEnd_3202045 := by
    simpa [prefixWord, tailWord_3202045, baseEnd_3202045] using wordTrace_append hprefix tailTrace_3202045
  have hstable : (prefixWord ++ tailWord_3202045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202045).length < 2 ^ (prefixWord ++ tailWord_3202045).sum := by decide
  have hdescent : baseEnd_3202045 < baseStart_3202045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202055 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 1, 6]
def baseStart_3202055 : Nat := 118140960795 + 3202055 * 2 ^ 59
def prefixEnd_3202055 : Nat := 4983230072969 + 3 ^ 40 * 3202055 * 2
def baseEnd_3202055 : Nat := 548064432377524892928841

theorem tailTrace_3202055 : CollatzResearch.WordTrace tailWord_3202055 prefixEnd_3202055 548064432377524892928841 := by
  unfold tailWord_3202055
  simp only [CollatzResearch.WordTrace]
  refine ⟨116788540414509077300767619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77859026943006051533845079 116788540414509077300767619)
  ·
    refine ⟨175182810621763615951151429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116788540414509077300767619 175182810621763615951151429)
    ·
      refine ⟨32846776991580677990840893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175182810621763615951151429 32846776991580677990840893)
      ·
        refine ⟨12317541371842754246565335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32846776991580677990840893 12317541371842754246565335)
        ·
          refine ⟨18476312057764131369848003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12317541371842754246565335 18476312057764131369848003)
          ·
            refine ⟨27714468086646197054772005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18476312057764131369848003 27714468086646197054772005)
            ·
              refine ⟨5196462766246161947769751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27714468086646197054772005 5196462766246161947769751)
              ·
                refine ⟨7794694149369242921654627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196462766246161947769751 7794694149369242921654627)
                ·
                  refine ⟨11692041224053864382481941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7794694149369242921654627 11692041224053864382481941)
                  ·
                    refine ⟨548064432377524892928841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11692041224053864382481941 548064432377524892928841)
                    ·
                      rfl

theorem cell23_3202055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_3202055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202055 prefixEnd_3202055 := by exact prefixLift 3202055
  have htrace : WordTrace (prefixWord ++ tailWord_3202055) baseStart_3202055 baseEnd_3202055 := by
    simpa [prefixWord, tailWord_3202055, baseEnd_3202055] using wordTrace_append hprefix tailTrace_3202055
  have hstable : (prefixWord ++ tailWord_3202055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202055).length < 2 ^ (prefixWord ++ tailWord_3202055).sum := by decide
  have hdescent : baseEnd_3202055 < baseStart_3202055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202076 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_3202076 : Nat := 118140960795 + 3202076 * 2 ^ 59
def prefixEnd_3202076 : Nat := 4983230072969 + 3 ^ 40 * 3202076 * 2
def baseEnd_3202076 : Nat := 548068026742106365541309

theorem tailTrace_3202076 : CollatzResearch.WordTrace tailWord_3202076 prefixEnd_3202076 548068026742106365541309 := by
  unfold tailWord_3202076
  simp only [CollatzResearch.WordTrace]
  refine ⟨58394653173716498943641041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77859537564955331924854721 58394653173716498943641041)
  ·
    refine ⟨43795989880287374207730781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58394653173716498943641041 43795989880287374207730781)
    ·
      refine ⟨16423496205107765327899043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43795989880287374207730781 16423496205107765327899043)
      ·
        refine ⟨24635244307661647991848565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16423496205107765327899043 24635244307661647991848565)
        ·
          refine ⟨2309554153843279499235803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24635244307661647991848565 2309554153843279499235803)
          ·
            refine ⟨3464331230764919248853705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309554153843279499235803 3464331230764919248853705)
            ·
              refine ⟨2598248423073689436640279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464331230764919248853705 2598248423073689436640279)
              ·
                refine ⟨3897372634610534154960419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598248423073689436640279 3897372634610534154960419)
                ·
                  refine ⟨5846058951915801232440629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897372634610534154960419 5846058951915801232440629)
                  ·
                    refine ⟨548068026742106365541309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5846058951915801232440629 548068026742106365541309)
                    ·
                      rfl

theorem cell23_3202076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_3202076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202076 prefixEnd_3202076 := by exact prefixLift 3202076
  have htrace : WordTrace (prefixWord ++ tailWord_3202076) baseStart_3202076 baseEnd_3202076 := by
    simpa [prefixWord, tailWord_3202076, baseEnd_3202076] using wordTrace_append hprefix tailTrace_3202076
  have hstable : (prefixWord ++ tailWord_3202076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202076).length < 2 ^ (prefixWord ++ tailWord_3202076).sum := by decide
  have hdescent : baseEnd_3202076 < baseStart_3202076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202079 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 1, 1, 4]
def baseStart_3202079 : Nat := 118140960795 + 3202079 * 2 ^ 59
def prefixEnd_3202079 : Nat := 4983230072969 + 3 ^ 40 * 3202079 * 2
def baseEnd_3202079 : Nat := 1644205620668282584886413

theorem tailTrace_3202079 : CollatzResearch.WordTrace tailWord_3202079 prefixEnd_3202079 1644205620668282584886413 := by
  unfold tailWord_3202079
  simp only [CollatzResearch.WordTrace]
  refine ⟨116789415766422129399641291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77859610510948086266427527 116789415766422129399641291)
  ·
    refine ⟨175184123649633194099461937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116789415766422129399641291 175184123649633194099461937)
    ·
      refine ⟨131388092737224895574596453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175184123649633194099461937 131388092737224895574596453)
      ·
        refine ⟨24635267388229667920236835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131388092737224895574596453 24635267388229667920236835)
        ·
          refine ⟨36952901082344501880355253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24635267388229667920236835 36952901082344501880355253)
          ·
            refine ⟨3464334476469797051283305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36952901082344501880355253 3464334476469797051283305)
            ·
              refine ⟨2598250857352347788462479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464334476469797051283305 2598250857352347788462479)
              ·
                refine ⟨3897376286028521682693719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598250857352347788462479 3897376286028521682693719)
                ·
                  refine ⟨5846064429042782524040579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897376286028521682693719 5846064429042782524040579)
                  ·
                    refine ⟨8769096643564173786060869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846064429042782524040579 8769096643564173786060869)
                    ·
                      refine ⟨1644205620668282584886413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8769096643564173786060869 1644205620668282584886413)
                      ·
                        rfl

theorem cell23_3202079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_3202079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202079 prefixEnd_3202079 := by exact prefixLift 3202079
  have htrace : WordTrace (prefixWord ++ tailWord_3202079) baseStart_3202079 baseEnd_3202079 := by
    simpa [prefixWord, tailWord_3202079, baseEnd_3202079] using wordTrace_append hprefix tailTrace_3202079
  have hstable : (prefixWord ++ tailWord_3202079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202079).length < 2 ^ (prefixWord ++ tailWord_3202079).sum := by decide
  have hdescent : baseEnd_3202079 < baseStart_3202079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202122 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2]
def baseStart_3202122 : Nat := 118140960795 + 3202122 * 2 ^ 59
def prefixEnd_3202122 : Nat := 4983230072969 + 3 ^ 40 * 3202122 * 2
def baseEnd_3202122 : Nat := 1644227700336425916648715

theorem tailTrace_3202122 : CollatzResearch.WordTrace tailWord_3202122 prefixEnd_3202122 1644227700336425916648715 := by
  unfold tailWord_3202122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29197746026316586935864155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77860656070177565162304413 29197746026316586935864155)
  ·
    refine ⟨43796619039474880403796233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29197746026316586935864155 43796619039474880403796233)
    ·
      refine ⟨32847464279606160302847175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43796619039474880403796233 32847464279606160302847175)
      ·
        refine ⟨49271196419409240454270763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32847464279606160302847175 49271196419409240454270763)
        ·
          refine ⟨73906794629113860681406145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49271196419409240454270763 73906794629113860681406145)
          ·
            refine ⟨55430095971835395511054609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73906794629113860681406145 55430095971835395511054609)
            ·
              refine ⟨41572571978876546633290957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55430095971835395511054609 41572571978876546633290957)
              ·
                refine ⟨15589714492078704987484109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41572571978876546633290957 15589714492078704987484109)
                ·
                  refine ⟨5846142934529514370306541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15589714492078704987484109 5846142934529514370306541)
                  ·
                    refine ⟨2192303600448567888864953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5846142934529514370306541 2192303600448567888864953)
                    ·
                      refine ⟨1644227700336425916648715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192303600448567888864953 1644227700336425916648715)
                      ·
                        rfl

theorem cell23_3202122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_3202122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202122 prefixEnd_3202122 := by exact prefixLift 3202122
  have htrace : WordTrace (prefixWord ++ tailWord_3202122) baseStart_3202122 baseEnd_3202122 := by
    simpa [prefixWord, tailWord_3202122, baseEnd_3202122] using wordTrace_append hprefix tailTrace_3202122
  have hstable : (prefixWord ++ tailWord_3202122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202122).length < 2 ^ (prefixWord ++ tailWord_3202122).sum := by decide
  have hdescent : baseEnd_3202122 < baseStart_3202122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202128 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_3202128 : Nat := 118140960795 + 3202128 * 2 ^ 59
def prefixEnd_3202128 : Nat := 4983230072969 + 3 ^ 40 * 3202128 * 2
def baseEnd_3202128 : Nat := 548076927073450964391229

theorem tailTrace_3202128 : CollatzResearch.WordTrace tailWord_3202128 prefixEnd_3202128 548076927073450964391229 := by
  unfold tailWord_3202128
  simp only [CollatzResearch.WordTrace]
  refine ⟨58395601471622305384087519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77860801962163073845450025 58395601471622305384087519)
  ·
    refine ⟨87593402207433458076131279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58395601471622305384087519 87593402207433458076131279)
    ·
      refine ⟨131390103311150187114196919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87593402207433458076131279 131390103311150187114196919)
      ·
        refine ⟨197085154966725280671295379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131390103311150187114196919 197085154966725280671295379)
        ·
          refine ⟨295627732450087921006943069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197085154966725280671295379 295627732450087921006943069)
          ·
            refine ⟨110860399668782970377603651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295627732450087921006943069 110860399668782970377603651)
            ·
              refine ⟨166290599503174455566405477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110860399668782970377603651 166290599503174455566405477)
              ·
                refine ⟨31179487406845210418701027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166290599503174455566405477 31179487406845210418701027)
                ·
                  refine ⟨46769231110267815628051541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31179487406845210418701027 46769231110267815628051541)
                  ·
                    refine ⟨548076927073450964391229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46769231110267815628051541 548076927073450964391229)
                    ·
                      rfl

theorem cell23_3202128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_3202128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202128 prefixEnd_3202128 := by exact prefixLift 3202128
  have htrace : WordTrace (prefixWord ++ tailWord_3202128) baseStart_3202128 baseEnd_3202128 := by
    simpa [prefixWord, tailWord_3202128, baseEnd_3202128] using wordTrace_append hprefix tailTrace_3202128
  have hstable : (prefixWord ++ tailWord_3202128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202128).length < 2 ^ (prefixWord ++ tailWord_3202128).sum := by decide
  have hdescent : baseEnd_3202128 < baseStart_3202128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202346 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3202346 : Nat := 118140960795 + 3202346 * 2 ^ 59
def prefixEnd_3202346 : Nat := 4983230072969 + 3 ^ 40 * 3202346 * 2
def baseEnd_3202346 : Nat := 548114240001011013415895

theorem tailTrace_3202346 : CollatzResearch.WordTrace tailWord_3202346 prefixEnd_3202346 548114240001011013415895 := by
  unfold tailWord_3202346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29199788514113708499902723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77866102704303222666407261 29199788514113708499902723)
  ·
    refine ⟨43799682771170562749854085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29199788514113708499902723 43799682771170562749854085)
    ·
      refine ⟨8212440519594480515597641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43799682771170562749854085 8212440519594480515597641)
      ·
        refine ⟨6159330389695860386698231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8212440519594480515597641 6159330389695860386698231)
        ·
          refine ⟨9238995584543790580047347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159330389695860386698231 9238995584543790580047347)
          ·
            refine ⟨13858493376815685870071021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9238995584543790580047347 13858493376815685870071021)
            ·
              refine ⟨5196935016305882201276633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13858493376815685870071021 5196935016305882201276633)
              ·
                refine ⟨3897701262229411650957475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5196935016305882201276633 3897701262229411650957475)
                ·
                  refine ⟨5846551893344117476436213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897701262229411650957475 5846551893344117476436213)
                  ·
                    refine ⟨548114240001011013415895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5846551893344117476436213 548114240001011013415895)
                    ·
                      rfl

theorem cell23_3202346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3202346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202346 prefixEnd_3202346 := by exact prefixLift 3202346
  have htrace : WordTrace (prefixWord ++ tailWord_3202346) baseStart_3202346 baseEnd_3202346 := by
    simpa [prefixWord, tailWord_3202346, baseEnd_3202346] using wordTrace_append hprefix tailTrace_3202346
  have hstable : (prefixWord ++ tailWord_3202346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202346).length < 2 ^ (prefixWord ++ tailWord_3202346).sum := by decide
  have hdescent : baseEnd_3202346 < baseStart_3202346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202389 : List Nat := [1, 3, 2, 2, 3, 3, 1, 8]
def baseStart_3202389 : Nat := 118140960795 + 3202389 * 2 ^ 59
def prefixEnd_3202389 : Nat := 4983230072969 + 3 ^ 40 * 3202389 * 2
def baseEnd_3202389 : Nat := 60902399987821347111481

theorem tailTrace_3202389 : CollatzResearch.WordTrace tailWord_3202389 prefixEnd_3202389 60902399987821347111481 := by
  unfold tailWord_3202389
  simp only [CollatzResearch.WordTrace]
  refine ⟨116800722395299052343426221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77867148263532701562284147 116800722395299052343426221)
  ·
    refine ⟨43800270898237144628784833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116800722395299052343426221 43800270898237144628784833)
    ·
      refine ⟨32850203173677858471588625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43800270898237144628784833 32850203173677858471588625)
      ·
        refine ⟨24637652380258393853691469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32850203173677858471588625 24637652380258393853691469)
        ·
          refine ⟨9239119642596897695134301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24637652380258393853691469 9239119642596897695134301)
          ·
            refine ⟨3464669865973836635675363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9239119642596897695134301 3464669865973836635675363)
            ·
              refine ⟨5197004798960754953513045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464669865973836635675363 5197004798960754953513045)
              ·
                refine ⟨60902399987821347111481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5197004798960754953513045 60902399987821347111481)
                ·
                  rfl

theorem cell23_3202389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 8].length) (baseStart_3202389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202389 prefixEnd_3202389 := by exact prefixLift 3202389
  have htrace : WordTrace (prefixWord ++ tailWord_3202389) baseStart_3202389 baseEnd_3202389 := by
    simpa [prefixWord, tailWord_3202389, baseEnd_3202389] using wordTrace_append hprefix tailTrace_3202389
  have hstable : (prefixWord ++ tailWord_3202389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202389).length < 2 ^ (prefixWord ++ tailWord_3202389).sum := by decide
  have hdescent : baseEnd_3202389 < baseStart_3202389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202399 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 3]
def baseStart_3202399 : Nat := 118140960795 + 3202399 * 2 ^ 59
def prefixEnd_3202399 : Nat := 4983230072969 + 3 ^ 40 * 3202399 * 2
def baseEnd_3202399 : Nat := 1644369934477721332884941

theorem tailTrace_3202399 : CollatzResearch.WordTrace tailWord_3202399 prefixEnd_3202399 1644369934477721332884941 := by
  unfold tailWord_3202399
  simp only [CollatzResearch.WordTrace]
  refine ⟨116801087125262824051290251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77867391416841882700860167 116801087125262824051290251)
  ·
    refine ⟨175201630687894236076935377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116801087125262824051290251 175201630687894236076935377)
    ·
      refine ⟨131401223015920677057701533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175201630687894236076935377 131401223015920677057701533)
      ·
        refine ⟨49275458630970253896638075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131401223015920677057701533 49275458630970253896638075)
        ·
          refine ⟨73913187946455380844957113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49275458630970253896638075 73913187946455380844957113)
          ·
            refine ⟨55434890959841535633717835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73913187946455380844957113 55434890959841535633717835)
            ·
              refine ⟨83152336439762303450576753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55434890959841535633717835 83152336439762303450576753)
              ·
                refine ⟨62364252329821727587932565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83152336439762303450576753 62364252329821727587932565)
                ·
                  refine ⟨2923324327960393480684339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62364252329821727587932565 2923324327960393480684339)
                  ·
                    refine ⟨4384986491940590221026509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923324327960393480684339 4384986491940590221026509)
                    ·
                      refine ⟨1644369934477721332884941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4384986491940590221026509 1644369934477721332884941)
                      ·
                        rfl

theorem cell23_3202399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_3202399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202399 prefixEnd_3202399 := by exact prefixLift 3202399
  have htrace : WordTrace (prefixWord ++ tailWord_3202399) baseStart_3202399 baseEnd_3202399 := by
    simpa [prefixWord, tailWord_3202399, baseEnd_3202399] using wordTrace_append hprefix tailTrace_3202399
  have hstable : (prefixWord ++ tailWord_3202399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202399).length < 2 ^ (prefixWord ++ tailWord_3202399).sum := by decide
  have hdescent : baseEnd_3202399 < baseStart_3202399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202426 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2]
def baseStart_3202426 : Nat := 118140960795 + 3202426 * 2 ^ 59
def prefixEnd_3202426 : Nat := 4983230072969 + 3 ^ 40 * 3202426 * 2
def baseEnd_3202426 : Nat := 1644383798455392727247317

theorem tailTrace_3202426 : CollatzResearch.WordTrace tailWord_3202426 prefixEnd_3202426 1644383798455392727247317 := by
  unfold tailWord_3202426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29200517974041251915630783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77868047930776671775015421 29200517974041251915630783)
  ·
    refine ⟨43800776961061877873446175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29200517974041251915630783 43800776961061877873446175)
    ·
      refine ⟨65701165441592816810169263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43800776961061877873446175 65701165441592816810169263)
      ·
        refine ⟨98551748162389225215253895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65701165441592816810169263 98551748162389225215253895)
        ·
          refine ⟨147827622243583837822880843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98551748162389225215253895 147827622243583837822880843)
          ·
            refine ⟨221741433365375756734321265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147827622243583837822880843 221741433365375756734321265)
            ·
              refine ⟨166306075024031817550740949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221741433365375756734321265 166306075024031817550740949)
              ·
                refine ⟨3897798633375745723845491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166306075024031817550740949 3897798633375745723845491)
                ·
                  refine ⟨5846697950063618585768237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897798633375745723845491 5846697950063618585768237)
                  ·
                    refine ⟨2192511731273856969663089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5846697950063618585768237 2192511731273856969663089)
                    ·
                      refine ⟨1644383798455392727247317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192511731273856969663089 1644383798455392727247317)
                      ·
                        rfl

theorem cell23_3202426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2].length) (baseStart_3202426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202426 prefixEnd_3202426 := by exact prefixLift 3202426
  have htrace : WordTrace (prefixWord ++ tailWord_3202426) baseStart_3202426 baseEnd_3202426 := by
    simpa [prefixWord, tailWord_3202426, baseEnd_3202426] using wordTrace_append hprefix tailTrace_3202426
  have hstable : (prefixWord ++ tailWord_3202426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202426).length < 2 ^ (prefixWord ++ tailWord_3202426).sum := by decide
  have hdescent : baseEnd_3202426 < baseStart_3202426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202433 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3202433 : Nat := 118140960795 + 3202433 * 2 ^ 59
def prefixEnd_3202433 : Nat := 4983230072969 + 3 ^ 40 * 3202433 * 2
def baseEnd_3202433 : Nat := 1644387392819974199859785

theorem tailTrace_3202433 : CollatzResearch.WordTrace tailWord_3202433 prefixEnd_3202433 1644387392819974199859785 := by
  unfold tailWord_3202433
  simp only [CollatzResearch.WordTrace]
  refine ⟨116802327207139647858027953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77868218138093098572018635 116802327207139647858027953)
  ·
    refine ⟨87601745405354735893520965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116802327207139647858027953 87601745405354735893520965)
    ·
      refine ⟨16425327263504012980035181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87601745405354735893520965 16425327263504012980035181)
      ·
        refine ⟨6159497723814004867513193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16425327263504012980035181 6159497723814004867513193)
        ·
          refine ⟨4619623292860503650634895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6159497723814004867513193 4619623292860503650634895)
          ·
            refine ⟨6929434939290755475952343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619623292860503650634895 6929434939290755475952343)
            ·
              refine ⟨10394152408936133213928515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929434939290755475952343 10394152408936133213928515)
              ·
                refine ⟨15591228613404199820892773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10394152408936133213928515 15591228613404199820892773)
                ·
                  refine ⟨2923355365013287466417395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15591228613404199820892773 2923355365013287466417395)
                  ·
                    refine ⟨4385033047519931199626093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923355365013287466417395 4385033047519931199626093)
                    ·
                      refine ⟨1644387392819974199859785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385033047519931199626093 1644387392819974199859785)
                      ·
                        rfl

theorem cell23_3202433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3202433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202433 prefixEnd_3202433 := by exact prefixLift 3202433
  have htrace : WordTrace (prefixWord ++ tailWord_3202433) baseStart_3202433 baseEnd_3202433 := by
    simpa [prefixWord, tailWord_3202433, baseEnd_3202433] using wordTrace_append hprefix tailTrace_3202433
  have hstable : (prefixWord ++ tailWord_3202433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202433).length < 2 ^ (prefixWord ++ tailWord_3202433).sum := by decide
  have hdescent : baseEnd_3202433 < baseStart_3202433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202450 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3202450 : Nat := 118140960795 + 3202450 * 2 ^ 59
def prefixEnd_3202450 : Nat := 4983230072969 + 3 ^ 40 * 3202450 * 2
def baseEnd_3202450 : Nat := 1644396121991100633347207

theorem tailTrace_3202450 : CollatzResearch.WordTrace tailWord_3202450 prefixEnd_3202450 1644396121991100633347207 := by
  unfold tailWord_3202450
  simp only [CollatzResearch.WordTrace]
  refine ⟨29200736812019514940349201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77868631498718706507597869 29200736812019514940349201)
  ·
    refine ⟨21900552609014636205261901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29200736812019514940349201 21900552609014636205261901)
    ·
      refine ⟨8212707228380488576973213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21900552609014636205261901 8212707228380488576973213)
      ·
        refine ⟨3079765210642683216364955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8212707228380488576973213 3079765210642683216364955)
        ·
          refine ⟨4619647815964024824547433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079765210642683216364955 4619647815964024824547433)
          ·
            refine ⟨3464735861973018618410575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619647815964024824547433 3464735861973018618410575)
            ·
              refine ⟨5197103792959527927615863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464735861973018618410575 5197103792959527927615863)
              ·
                refine ⟨7795655689439291891423795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5197103792959527927615863 7795655689439291891423795)
                ·
                  refine ⟨11693483534158937837135693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795655689439291891423795 11693483534158937837135693)
                  ·
                    refine ⟨4385056325309601688925885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11693483534158937837135693 4385056325309601688925885)
                    ·
                      refine ⟨1644396121991100633347207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385056325309601688925885 1644396121991100633347207)
                      ·
                        rfl

theorem cell23_3202450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3202450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202450 prefixEnd_3202450 := by exact prefixLift 3202450
  have htrace : WordTrace (prefixWord ++ tailWord_3202450) baseStart_3202450 baseEnd_3202450 := by
    simpa [prefixWord, tailWord_3202450, baseEnd_3202450] using wordTrace_append hprefix tailTrace_3202450
  have hstable : (prefixWord ++ tailWord_3202450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202450).length < 2 ^ (prefixWord ++ tailWord_3202450).sum := by decide
  have hdescent : baseEnd_3202450 < baseStart_3202450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202539 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 7, 4]
def baseStart_3202539 : Nat := 118140960795 + 3202539 * 2 ^ 59
def prefixEnd_3202539 : Nat := 4983230072969 + 3 ^ 40 * 3202539 * 2
def baseEnd_3202539 : Nat := 548147273923116928378099

theorem tailTrace_3202539 : CollatzResearch.WordTrace tailWord_3202539 prefixEnd_3202539 548147273923116928378099 := by
  unfold tailWord_3202539
  simp only [CollatzResearch.WordTrace]
  refine ⟨116806193344755627961386671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77870795563170418640924447 116806193344755627961386671)
  ·
    refine ⟨175209290017133441942080007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116806193344755627961386671 175209290017133441942080007)
    ·
      refine ⟨262813935025700162913120011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175209290017133441942080007 262813935025700162913120011)
      ·
        refine ⟨394220902538550244369680017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262813935025700162913120011 394220902538550244369680017)
        ·
          refine ⟨295665676903912683277260013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394220902538550244369680017 295665676903912683277260013)
          ·
            refine ⟨110874628838967256228972505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295665676903912683277260013 110874628838967256228972505)
            ·
              refine ⟨83155971629225442171729379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110874628838967256228972505 83155971629225442171729379)
              ·
                refine ⟨124733957443838163257594069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83155971629225442171729379 124733957443838163257594069)
                ·
                  refine ⟨2923452127589956951349861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 124733957443838163257594069 2923452127589956951349861)
                  ·
                    refine ⟨548147273923116928378099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2923452127589956951349861 548147273923116928378099)
                    ·
                      rfl

theorem cell23_3202539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 4].length) (baseStart_3202539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202539 prefixEnd_3202539 := by exact prefixLift 3202539
  have htrace : WordTrace (prefixWord ++ tailWord_3202539) baseStart_3202539 baseEnd_3202539 := by
    simpa [prefixWord, tailWord_3202539, baseEnd_3202539] using wordTrace_append hprefix tailTrace_3202539
  have hstable : (prefixWord ++ tailWord_3202539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202539).length < 2 ^ (prefixWord ++ tailWord_3202539).sum := by decide
  have hdescent : baseEnd_3202539 < baseStart_3202539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202569 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 6]
def baseStart_3202569 : Nat := 118140960795 + 3202569 * 2 ^ 59
def prefixEnd_3202569 : Nat := 4983230072969 + 3 ^ 40 * 3202569 * 2
def baseEnd_3202569 : Nat := 182717469576553963084351

theorem tailTrace_3202569 : CollatzResearch.WordTrace tailWord_3202569 prefixEnd_3202569 182717469576553963084351 := by
  unfold tailWord_3202569
  simp only [CollatzResearch.WordTrace]
  refine ⟨116807287534646943084978761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77871525023097962056652507 116807287534646943084978761)
  ·
    refine ⟨87605465650985207313734071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116807287534646943084978761 87605465650985207313734071)
    ·
      refine ⟨131408198476477810970601107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87605465650985207313734071 131408198476477810970601107)
      ·
        refine ⟨197112297714716716455901661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131408198476477810970601107 197112297714716716455901661)
        ·
          refine ⟨73917111643018768670963123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197112297714716716455901661 73917111643018768670963123)
          ·
            refine ⟨110875667464528153006444685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73917111643018768670963123 110875667464528153006444685)
            ·
              refine ⟨41578375299198057377416757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110875667464528153006444685 41578375299198057377416757)
              ·
                refine ⟨3897972684299817879132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41578375299198057377416757 3897972684299817879132821)
                ·
                  refine ⟨182717469576553963084351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3897972684299817879132821 182717469576553963084351)
                  ·
                    rfl

theorem cell23_3202569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_3202569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202569 prefixEnd_3202569 := by exact prefixLift 3202569
  have htrace : WordTrace (prefixWord ++ tailWord_3202569) baseStart_3202569 baseEnd_3202569 := by
    simpa [prefixWord, tailWord_3202569, baseEnd_3202569] using wordTrace_append hprefix tailTrace_3202569
  have hstable : (prefixWord ++ tailWord_3202569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202569).length < 2 ^ (prefixWord ++ tailWord_3202569).sum := by decide
  have hdescent : baseEnd_3202569 < baseStart_3202569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202606 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3202606 : Nat := 118140960795 + 3202606 * 2 ^ 59
def prefixEnd_3202606 : Nat := 4983230072969 + 3 ^ 40 * 3202606 * 2
def baseEnd_3202606 : Nat := 1644476224973202022996489

theorem tailTrace_3202606 : CollatzResearch.WordTrace tailWord_3202606 prefixEnd_3202606 1644476224973202022996489 := by
  unfold tailWord_3202606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601079629439112300509459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77872424690341932269383781 14601079629439112300509459)
  ·
    refine ⟨21901619444158668450764189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14601079629439112300509459 21901619444158668450764189)
    ·
      refine ⟨8213107291559500669036571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21901619444158668450764189 8213107291559500669036571)
      ·
        refine ⟨12319660937339251003554857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8213107291559500669036571 12319660937339251003554857)
        ·
          refine ⟨9239745703004438252666143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12319660937339251003554857 9239745703004438252666143)
          ·
            refine ⟨13859618554506657378999215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9239745703004438252666143 13859618554506657378999215)
            ·
              refine ⟨20789427831759986068498823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13859618554506657378999215 20789427831759986068498823)
              ·
                refine ⟨31184141747639979102748235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20789427831759986068498823 31184141747639979102748235)
                ·
                  refine ⟨46776212621459968654122353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31184141747639979102748235 46776212621459968654122353)
                  ·
                    refine ⟨35082159466094976490591765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46776212621459968654122353 35082159466094976490591765)
                    ·
                      refine ⟨1644476224973202022996489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35082159466094976490591765 1644476224973202022996489)
                      ·
                        rfl

theorem cell23_3202606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3202606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202606 prefixEnd_3202606 := by exact prefixLift 3202606
  have htrace : WordTrace (prefixWord ++ tailWord_3202606) baseStart_3202606 baseEnd_3202606 := by
    simpa [prefixWord, tailWord_3202606, baseEnd_3202606] using wordTrace_append hprefix tailTrace_3202606
  have hstable : (prefixWord ++ tailWord_3202606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202606).length < 2 ^ (prefixWord ++ tailWord_3202606).sum := by decide
  have hdescent : baseEnd_3202606 < baseStart_3202606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202613 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_3202613 : Nat := 118140960795 + 3202613 * 2 ^ 59
def prefixEnd_3202613 : Nat := 4983230072969 + 3 ^ 40 * 3202613 * 2
def baseEnd_3202613 : Nat := 1644479819337783495608957

theorem tailTrace_3202613 : CollatzResearch.WordTrace tailWord_3202613 prefixEnd_3202613 1644479819337783495608957 := by
  unfold tailWord_3202613
  simp only [CollatzResearch.WordTrace]
  refine ⟨116808892346487538599580493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77872594897658359066386995 116808892346487538599580493)
  ·
    refine ⟨43803334629932826974842685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116808892346487538599580493 43803334629932826974842685)
    ·
      refine ⟨16426250486224810115566007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43803334629932826974842685 16426250486224810115566007)
      ·
        refine ⟨24639375729337215173349011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16426250486224810115566007 24639375729337215173349011)
        ·
          refine ⟨36959063594005822760023517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24639375729337215173349011 36959063594005822760023517)
          ·
            refine ⟨13859648847752183535008819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36959063594005822760023517 13859648847752183535008819)
            ·
              refine ⟨20789473271628275302513229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13859648847752183535008819 20789473271628275302513229)
              ·
                refine ⟨7796052476860603238442461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20789473271628275302513229 7796052476860603238442461)
                ·
                  refine ⟨2923519678822726214415923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7796052476860603238442461 2923519678822726214415923)
                  ·
                    refine ⟨4385279518234089321623885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923519678822726214415923 4385279518234089321623885)
                    ·
                      refine ⟨1644479819337783495608957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385279518234089321623885 1644479819337783495608957)
                      ·
                        rfl

theorem cell23_3202613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_3202613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202613 prefixEnd_3202613 := by exact prefixLift 3202613
  have htrace : WordTrace (prefixWord ++ tailWord_3202613) baseStart_3202613 baseEnd_3202613 := by
    simpa [prefixWord, tailWord_3202613, baseEnd_3202613] using wordTrace_append hprefix tailTrace_3202613
  have hstable : (prefixWord ++ tailWord_3202613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202613).length < 2 ^ (prefixWord ++ tailWord_3202613).sum := by decide
  have hdescent : baseEnd_3202613 < baseStart_3202613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202639 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_3202639 : Nat := 118140960795 + 3202639 * 2 ^ 59
def prefixEnd_3202639 : Nat := 4983230072969 + 3 ^ 40 * 3202639 * 2
def baseEnd_3202639 : Nat := 1644493169834800393883837

theorem tailTrace_3202639 : CollatzResearch.WordTrace tailWord_3202639 prefixEnd_3202639 1644493169834800393883837 := by
  unfold tailWord_3202639
  simp only [CollatzResearch.WordTrace]
  refine ⟨116809840644393345040026971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77873227096262230026684647 116809840644393345040026971)
  ·
    refine ⟨175214760966590017560040457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116809840644393345040026971 175214760966590017560040457)
    ·
      refine ⟨131411070724942513170030343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175214760966590017560040457 131411070724942513170030343)
      ·
        refine ⟨197116606087413769755045515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131411070724942513170030343 197116606087413769755045515)
        ·
          refine ⟨295674909131120654632568273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197116606087413769755045515 295674909131120654632568273)
          ·
            refine ⟨221756181848340490974426205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295674909131120654632568273 221756181848340490974426205)
            ·
              refine ⟨83158568193127684115409827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221756181848340490974426205 83158568193127684115409827)
              ·
                refine ⟨124737852289691526173114741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83158568193127684115409827 124737852289691526173114741)
                ·
                  refine ⟨11694173652158580578729507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124737852289691526173114741 11694173652158580578729507)
                  ·
                    refine ⟨17541260478237870868094261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11694173652158580578729507 17541260478237870868094261)
                    ·
                      refine ⟨1644493169834800393883837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17541260478237870868094261 1644493169834800393883837)
                      ·
                        rfl

theorem cell23_3202639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_3202639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202639 prefixEnd_3202639 := by exact prefixLift 3202639
  have htrace : WordTrace (prefixWord ++ tailWord_3202639) baseStart_3202639 baseEnd_3202639 := by
    simpa [prefixWord, tailWord_3202639, baseEnd_3202639] using wordTrace_append hprefix tailTrace_3202639
  have hstable : (prefixWord ++ tailWord_3202639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202639).length < 2 ^ (prefixWord ++ tailWord_3202639).sum := by decide
  have hdescent : baseEnd_3202639 < baseStart_3202639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202647 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 1, 1, 3]
def baseStart_3202647 : Nat := 118140960795 + 3202647 * 2 ^ 59
def prefixEnd_3202647 : Nat := 4983230072969 + 3 ^ 40 * 3202647 * 2
def baseEnd_3202647 : Nat := 1644497277680036362583801

theorem tailTrace_3202647 : CollatzResearch.WordTrace tailWord_3202647 prefixEnd_3202647 1644497277680036362583801 := by
  unfold tailWord_3202647
  simp only [CollatzResearch.WordTrace]
  refine ⟨116810132428364362406318195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77873421618909574937545463 116810132428364362406318195)
  ·
    refine ⟨175215198642546543609477293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116810132428364362406318195 175215198642546543609477293)
    ·
      refine ⟨65705699490954953853553985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175215198642546543609477293 65705699490954953853553985)
      ·
        refine ⟨49279274618216215390165489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65705699490954953853553985 49279274618216215390165489)
        ·
          refine ⟨36959455963662161542624117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49279274618216215390165489 36959455963662161542624117)
          ·
            refine ⟨3464948996593327644621011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36959455963662161542624117 3464948996593327644621011)
            ·
              refine ⟨5197423494889991466931517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464948996593327644621011 5197423494889991466931517)
              ·
                refine ⟨1949033810583746800099319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5197423494889991466931517 1949033810583746800099319)
                ·
                  refine ⟨2923550715875620200148979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949033810583746800099319 2923550715875620200148979)
                  ·
                    refine ⟨4385326073813430300223469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923550715875620200148979 4385326073813430300223469)
                    ·
                      refine ⟨1644497277680036362583801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385326073813430300223469 1644497277680036362583801)
                      ·
                        rfl

theorem cell23_3202647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_3202647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202647 prefixEnd_3202647 := by exact prefixLift 3202647
  have htrace : WordTrace (prefixWord ++ tailWord_3202647) baseStart_3202647 baseEnd_3202647 := by
    simpa [prefixWord, tailWord_3202647, baseEnd_3202647] using wordTrace_append hprefix tailTrace_3202647
  have hstable : (prefixWord ++ tailWord_3202647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202647).length < 2 ^ (prefixWord ++ tailWord_3202647).sum := by decide
  have hdescent : baseEnd_3202647 < baseStart_3202647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202656 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3202656 : Nat := 118140960795 + 3202656 * 2 ^ 59
def prefixEnd_3202656 : Nat := 4983230072969 + 3 ^ 40 * 3202656 * 2
def baseEnd_3202656 : Nat := 1644501899005926827371259

theorem tailTrace_3202656 : CollatzResearch.WordTrace tailWord_3202656 prefixEnd_3202656 1644501899005926827371259 := by
  unfold tailWord_3202656
  simp only [CollatzResearch.WordTrace]
  refine ⟨58405230342665878471697911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77873640456887837962263881 58405230342665878471697911)
  ·
    refine ⟨87607845513998817707546867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58405230342665878471697911 87607845513998817707546867)
    ·
      refine ⟨131411768270998226561320301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87607845513998817707546867 131411768270998226561320301)
      ·
        refine ⟨49279413101624334960495113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131411768270998226561320301 49279413101624334960495113)
        ·
          refine ⟨36959559826218251220371335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49279413101624334960495113 36959559826218251220371335)
          ·
            refine ⟨55439339739327376830557003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36959559826218251220371335 55439339739327376830557003)
            ·
              refine ⟨83159009608991065245835505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55439339739327376830557003 83159009608991065245835505)
              ·
                refine ⟨62369257206743298934376629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83159009608991065245835505 62369257206743298934376629)
                ·
                  refine ⟨5847117863132184275097809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62369257206743298934376629 5847117863132184275097809)
                  ·
                    refine ⟨4385338397349138206323357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5847117863132184275097809 4385338397349138206323357)
                    ·
                      refine ⟨1644501899005926827371259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385338397349138206323357 1644501899005926827371259)
                      ·
                        rfl

theorem cell23_3202656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3202656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202656 prefixEnd_3202656 := by exact prefixLift 3202656
  have htrace : WordTrace (prefixWord ++ tailWord_3202656) baseStart_3202656 baseEnd_3202656 := by
    simpa [prefixWord, tailWord_3202656, baseEnd_3202656] using wordTrace_append hprefix tailTrace_3202656
  have hstable : (prefixWord ++ tailWord_3202656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202656).length < 2 ^ (prefixWord ++ tailWord_3202656).sum := by decide
  have hdescent : baseEnd_3202656 < baseStart_3202656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202659 : List Nat := [1, 1, 1, 5, 1, 3, 11]
def baseStart_3202659 : Nat := 118140960795 + 3202659 * 2 ^ 59
def prefixEnd_3202659 : Nat := 4983230072969 + 3 ^ 40 * 3202659 * 2
def baseEnd_3202659 : Nat := 20302511598122102662145

theorem tailTrace_3202659 : CollatzResearch.WordTrace tailWord_3202659 prefixEnd_3202659 20302511598122102662145 := by
  unfold tailWord_3202659
  simp only [CollatzResearch.WordTrace]
  refine ⟨116810570104320888455755031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77873713402880592303836687 116810570104320888455755031)
  ·
    refine ⟨175215855156481332683632547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116810570104320888455755031 175215855156481332683632547)
    ·
      refine ⟨262823782734721999025448821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175215855156481332683632547 262823782734721999025448821)
      ·
        refine ⟨24639729631380187408635827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262823782734721999025448821 24639729631380187408635827)
        ·
          refine ⟨36959594447070281112953741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24639729631380187408635827 36959594447070281112953741)
          ·
            refine ⟨13859847917651355417357653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36959594447070281112953741 13859847917651355417357653)
            ·
              refine ⟨20302511598122102662145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13859847917651355417357653 20302511598122102662145)
              ·
                rfl

theorem cell23_3202659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 11].length) (baseStart_3202659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202659 prefixEnd_3202659 := by exact prefixLift 3202659
  have htrace : WordTrace (prefixWord ++ tailWord_3202659) baseStart_3202659 baseEnd_3202659 := by
    simpa [prefixWord, tailWord_3202659, baseEnd_3202659] using wordTrace_append hprefix tailTrace_3202659
  have hstable : (prefixWord ++ tailWord_3202659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202659).length < 2 ^ (prefixWord ++ tailWord_3202659).sum := by decide
  have hdescent : baseEnd_3202659 < baseStart_3202659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202664 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3202664 : Nat := 118140960795 + 3202664 * 2 ^ 59
def prefixEnd_3202664 : Nat := 4983230072969 + 3 ^ 40 * 3202664 * 2
def baseEnd_3202664 : Nat := 1644506006851162796071223

theorem tailTrace_3202664 : CollatzResearch.WordTrace tailWord_3202664 prefixEnd_3202664 1644506006851162796071223 := by
  unfold tailWord_3202664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58405376234651387154843523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77873834979535182873124697 58405376234651387154843523)
  ·
    refine ⟨87608064351977080732265285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58405376234651387154843523 87608064351977080732265285)
    ·
      refine ⟨16426512065995702637299741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87608064351977080732265285 16426512065995702637299741)
      ·
        refine ⟨6159942024748388488987403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16426512065995702637299741 6159942024748388488987403)
        ·
          refine ⟨9239913037122582733481105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159942024748388488987403 9239913037122582733481105)
          ·
            refine ⟨6929934777841937050110829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9239913037122582733481105 6929934777841937050110829)
            ·
              refine ⟨2598725541690726393791561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6929934777841937050110829 2598725541690726393791561)
              ·
                refine ⟨1949044156268044795343671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598725541690726393791561 1949044156268044795343671)
                ·
                  refine ⟨2923566234402067193015507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949044156268044795343671 2923566234402067193015507)
                  ·
                    refine ⟨4385349351603100789523261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923566234402067193015507 4385349351603100789523261)
                    ·
                      refine ⟨1644506006851162796071223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385349351603100789523261 1644506006851162796071223)
                      ·
                        rfl

theorem cell23_3202664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3202664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202664 prefixEnd_3202664 := by exact prefixLift 3202664
  have htrace : WordTrace (prefixWord ++ tailWord_3202664) baseStart_3202664 baseEnd_3202664 := by
    simpa [prefixWord, tailWord_3202664, baseEnd_3202664] using wordTrace_append hprefix tailTrace_3202664
  have hstable : (prefixWord ++ tailWord_3202664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202664).length < 2 ^ (prefixWord ++ tailWord_3202664).sum := by decide
  have hdescent : baseEnd_3202664 < baseStart_3202664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202666 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3202666 : Nat := 118140960795 + 3202666 * 2 ^ 59
def prefixEnd_3202666 : Nat := 4983230072969 + 3 ^ 40 * 3202666 * 2
def baseEnd_3202666 : Nat := 1644507033812471788246213

theorem tailTrace_3202666 : CollatzResearch.WordTrace tailWord_3202666 prefixEnd_3202666 1644507033812471788246213 := by
  unfold tailWord_3202666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29202706353823882162814963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77873883610197019100839901 29202706353823882162814963)
  ·
    refine ⟨43804059530735823244222445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29202706353823882162814963 43804059530735823244222445)
    ·
      refine ⟨16426522324025933716583417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43804059530735823244222445 16426522324025933716583417)
      ·
        refine ⟨12319891743019450287437563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16426522324025933716583417 12319891743019450287437563)
        ·
          refine ⟨18479837614529175431156345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12319891743019450287437563 18479837614529175431156345)
          ·
            refine ⟨13859878210896881573367259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18479837614529175431156345 13859878210896881573367259)
            ·
              refine ⟨20789817316345322360050889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13859878210896881573367259 20789817316345322360050889)
              ·
                refine ⟨15592362987258991770038167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20789817316345322360050889 15592362987258991770038167)
                ·
                  refine ⟨23388544480888487655057251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15592362987258991770038167 23388544480888487655057251)
                  ·
                    refine ⟨35082816721332731482585877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23388544480888487655057251 35082816721332731482585877)
                    ·
                      refine ⟨1644507033812471788246213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35082816721332731482585877 1644507033812471788246213)
                      ·
                        rfl

theorem cell23_3202666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3202666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202666 prefixEnd_3202666 := by exact prefixLift 3202666
  have htrace : WordTrace (prefixWord ++ tailWord_3202666) baseStart_3202666 baseEnd_3202666 := by
    simpa [prefixWord, tailWord_3202666, baseEnd_3202666] using wordTrace_append hprefix tailTrace_3202666
  have hstable : (prefixWord ++ tailWord_3202666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202666).length < 2 ^ (prefixWord ++ tailWord_3202666).sum := by decide
  have hdescent : baseEnd_3202666 < baseStart_3202666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202679 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3202679 : Nat := 118140960795 + 3202679 * 2 ^ 59
def prefixEnd_3202679 : Nat := 4983230072969 + 3 ^ 40 * 3202679 * 2
def baseEnd_3202679 : Nat := 1644513709060980237383653

theorem tailTrace_3202679 : CollatzResearch.WordTrace tailWord_3202679 prefixEnd_3202679 1644513709060980237383653 := by
  unfold tailWord_3202679
  simp only [CollatzResearch.WordTrace]
  refine ⟨116811299564248431871483091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77874199709498954580988727 116811299564248431871483091)
  ·
    refine ⟨175216949346372647807224637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116811299564248431871483091 175216949346372647807224637)
    ·
      refine ⟨65706356004889742927709239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175216949346372647807224637 65706356004889742927709239)
      ·
        refine ⟨98559534007334614391563859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65706356004889742927709239 98559534007334614391563859)
        ·
          refine ⟨147839301011001921587345789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98559534007334614391563859 147839301011001921587345789)
          ·
            refine ⟨55439737879125720595254671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147839301011001921587345789 55439737879125720595254671)
            ·
              refine ⟨83159606818688580892882007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55439737879125720595254671 83159606818688580892882007)
              ·
                refine ⟨124739410228032871339323011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83159606818688580892882007 124739410228032871339323011)
                ·
                  refine ⟨187109115342049307008984517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124739410228032871339323011 187109115342049307008984517)
                  ·
                    refine ⟨35082959126634245064184597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187109115342049307008984517 35082959126634245064184597)
                    ·
                      refine ⟨1644513709060980237383653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35082959126634245064184597 1644513709060980237383653)
                      ·
                        rfl

theorem cell23_3202679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3202679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202679 prefixEnd_3202679 := by exact prefixLift 3202679
  have htrace : WordTrace (prefixWord ++ tailWord_3202679) baseStart_3202679 baseEnd_3202679 := by
    simpa [prefixWord, tailWord_3202679, baseEnd_3202679] using wordTrace_append hprefix tailTrace_3202679
  have hstable : (prefixWord ++ tailWord_3202679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202679).length < 2 ^ (prefixWord ++ tailWord_3202679).sum := by decide
  have hdescent : baseEnd_3202679 < baseStart_3202679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202720 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3202720 : Nat := 118140960795 + 3202720 * 2 ^ 59
def prefixEnd_3202720 : Nat := 4983230072969 + 3 ^ 40 * 3202720 * 2
def baseEnd_3202720 : Nat := 1644534761767814576970965

theorem tailTrace_3202720 : CollatzResearch.WordTrace tailWord_3202720 prefixEnd_3202720 1644534761767814576970965 := by
  unfold tailWord_3202720
  simp only [CollatzResearch.WordTrace]
  refine ⟨58406397478549947936862807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77875196638066597249150409 58406397478549947936862807)
  ·
    refine ⟨87609596217824921905294211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58406397478549947936862807 87609596217824921905294211)
    ·
      refine ⟨131414394326737382857941317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87609596217824921905294211 131414394326737382857941317)
      ·
        refine ⟨24640198936263259285863997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131414394326737382857941317 24640198936263259285863997)
        ·
          refine ⟨9240074601098722232198999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24640198936263259285863997 9240074601098722232198999)
          ·
            refine ⟨13860111901648083348298499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9240074601098722232198999 13860111901648083348298499)
            ·
              refine ⟨20790167852472125022447749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13860111901648083348298499 20790167852472125022447749)
              ·
                refine ⟨3898156472338523441708953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20790167852472125022447749 3898156472338523441708953)
                ·
                  refine ⟨2923617354253892581281715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898156472338523441708953 2923617354253892581281715)
                  ·
                    refine ⟨4385426031380838871922573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923617354253892581281715 4385426031380838871922573)
                    ·
                      refine ⟨1644534761767814576970965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385426031380838871922573 1644534761767814576970965)
                      ·
                        rfl

theorem cell23_3202720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3202720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202720 prefixEnd_3202720 := by exact prefixLift 3202720
  have htrace : WordTrace (prefixWord ++ tailWord_3202720) baseStart_3202720 baseEnd_3202720 := by
    simpa [prefixWord, tailWord_3202720, baseEnd_3202720] using wordTrace_append hprefix tailTrace_3202720
  have hstable : (prefixWord ++ tailWord_3202720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202720).length < 2 ^ (prefixWord ++ tailWord_3202720).sum := by decide
  have hdescent : baseEnd_3202720 < baseStart_3202720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202721 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3202721 : Nat := 118140960795 + 3202721 * 2 ^ 59
def prefixEnd_3202721 : Nat := 4983230072969 + 3 ^ 40 * 3202721 * 2
def baseEnd_3202721 : Nat := 1644535275248469073058461

theorem tailTrace_3202721 : CollatzResearch.WordTrace tailWord_3202721 prefixEnd_3202721 1644535275248469073058461 := by
  unfold tailWord_3202721
  simp only [CollatzResearch.WordTrace]
  refine ⟨116812831430096273044512017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77875220953397515363008011 116812831430096273044512017)
  ·
    refine ⟨87609623572572204783384013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116812831430096273044512017 87609623572572204783384013)
    ·
      refine ⟨32853608839714576793769005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87609623572572204783384013 32853608839714576793769005)
      ·
        refine ⟨12320103314892966297663377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32853608839714576793769005 12320103314892966297663377)
        ·
          refine ⟨9240077486169724723247533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12320103314892966297663377 9240077486169724723247533)
          ·
            refine ⟨3465029057313646771217825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9240077486169724723247533 3465029057313646771217825)
            ·
              refine ⟨2598771792985235078413369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465029057313646771217825 2598771792985235078413369)
              ·
                refine ⟨1949078844738926308810027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598771792985235078413369 1949078844738926308810027)
                ·
                  refine ⟨2923618267108389463215041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949078844738926308810027 2923618267108389463215041)
                  ·
                    refine ⟨2192713700331292097411281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2923618267108389463215041 2192713700331292097411281)
                    ·
                      refine ⟨1644535275248469073058461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192713700331292097411281 1644535275248469073058461)
                      ·
                        rfl

theorem cell23_3202721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3202721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202721 prefixEnd_3202721 := by exact prefixLift 3202721
  have htrace : WordTrace (prefixWord ++ tailWord_3202721) baseStart_3202721 baseEnd_3202721 := by
    simpa [prefixWord, tailWord_3202721, baseEnd_3202721] using wordTrace_append hprefix tailTrace_3202721
  have hstable : (prefixWord ++ tailWord_3202721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202721).length < 2 ^ (prefixWord ++ tailWord_3202721).sum := by decide
  have hdescent : baseEnd_3202721 < baseStart_3202721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202760 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_3202760 : Nat := 118140960795 + 3202760 * 2 ^ 59
def prefixEnd_3202760 : Nat := 4983230072969 + 3 ^ 40 * 3202760 * 2
def baseEnd_3202760 : Nat := 1644555300993994420470781

theorem tailTrace_3202760 : CollatzResearch.WordTrace tailWord_3202760 prefixEnd_3202760 1644555300993994420470781 := by
  unfold tailWord_3202760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58407126938477491352590867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77876169251303321803454489 58407126938477491352590867)
  ·
    refine ⟨87610690407716237028886301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58407126938477491352590867 87610690407716237028886301)
    ·
      refine ⟨32854008902893588885832363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87610690407716237028886301 32854008902893588885832363)
      ·
        refine ⟨49281013354340383328748545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32854008902893588885832363 49281013354340383328748545)
        ·
          refine ⟨36960760015755287496561409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49281013354340383328748545 36960760015755287496561409)
          ·
            refine ⟨27720570011816465622421057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36960760015755287496561409 27720570011816465622421057)
            ·
              refine ⟨20790427508862349216815793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27720570011816465622421057 20790427508862349216815793)
              ·
                refine ⟨15592820631646761912611845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20790427508862349216815793 15592820631646761912611845)
                ·
                  refine ⟨2923653868433767858614721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15592820631646761912611845 2923653868433767858614721)
                  ·
                    refine ⟨2192740401325325893961041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2923653868433767858614721 2192740401325325893961041)
                    ·
                      refine ⟨1644555300993994420470781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192740401325325893961041 1644555300993994420470781)
                      ·
                        rfl

theorem cell23_3202760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_3202760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202760 prefixEnd_3202760 := by exact prefixLift 3202760
  have htrace : WordTrace (prefixWord ++ tailWord_3202760) baseStart_3202760 baseEnd_3202760 := by
    simpa [prefixWord, tailWord_3202760, baseEnd_3202760] using wordTrace_append hprefix tailTrace_3202760
  have hstable : (prefixWord ++ tailWord_3202760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202760).length < 2 ^ (prefixWord ++ tailWord_3202760).sum := by decide
  have hdescent : baseEnd_3202760 < baseStart_3202760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202766 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_3202766 : Nat := 118140960795 + 3202766 * 2 ^ 59
def prefixEnd_3202766 : Nat := 4983230072969 + 3 ^ 40 * 3202766 * 2
def baseEnd_3202766 : Nat := 182728709097546821888417

theorem tailTrace_3202766 : CollatzResearch.WordTrace tailWord_3202766 prefixEnd_3202766 182728709097546821888417 := by
  unfold tailWord_3202766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601809089366655716237519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77876315143288830486600101 14601809089366655716237519)
  ·
    refine ⟨21902713634049983574356279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14601809089366655716237519 21902713634049983574356279)
    ·
      refine ⟨32854070451074975361534419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21902713634049983574356279 32854070451074975361534419)
      ·
        refine ⟨49281105676612463042301629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32854070451074975361534419 49281105676612463042301629)
        ·
          refine ⟨18480414628729673640863111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49281105676612463042301629 18480414628729673640863111)
          ·
            refine ⟨27720621943094510461294667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18480414628729673640863111 27720621943094510461294667)
            ·
              refine ⟨41580932914641765691942001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27720621943094510461294667 41580932914641765691942001)
              ·
                refine ⟨31185699685981324268956501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41580932914641765691942001 31185699685981324268956501)
                ·
                  refine ⟨182728709097546821888417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31185699685981324268956501 182728709097546821888417)
                  ·
                    rfl

theorem cell23_3202766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_3202766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202766 prefixEnd_3202766 := by exact prefixLift 3202766
  have htrace : WordTrace (prefixWord ++ tailWord_3202766) baseStart_3202766 baseEnd_3202766 := by
    simpa [prefixWord, tailWord_3202766, baseEnd_3202766] using wordTrace_append hprefix tailTrace_3202766
  have hstable : (prefixWord ++ tailWord_3202766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202766).length < 2 ^ (prefixWord ++ tailWord_3202766).sum := by decide
  have hdescent : baseEnd_3202766 < baseStart_3202766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202777 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 2, 2, 2]
def baseStart_3202777 : Nat := 118140960795 + 3202777 * 2 ^ 59
def prefixEnd_3202777 : Nat := 4983230072969 + 3 ^ 40 * 3202777 * 2
def baseEnd_3202777 : Nat := 1644564030165120853958203

theorem tailTrace_3202777 : CollatzResearch.WordTrace tailWord_3202777 prefixEnd_3202777 1644564030165120853958203 := by
  unfold tailWord_3202777
  simp only [CollatzResearch.WordTrace]
  refine ⟨116814873917893394608550585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77876582611928929739033723 116814873917893394608550585)
  ·
    refine ⟨87611155438420045956412939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116814873917893394608550585 87611155438420045956412939)
    ·
      refine ⟨131416733157630068934619409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87611155438420045956412939 131416733157630068934619409)
      ·
        refine ⟨98562549868222551700964557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131416733157630068934619409 98562549868222551700964557)
        ·
          refine ⟨36960956200583456887861709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98562549868222551700964557 36960956200583456887861709)
          ·
            refine ⟨13860358575218796332948141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36960956200583456887861709 13860358575218796332948141)
            ·
              refine ⟨5197634465707048624855553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13860358575218796332948141 5197634465707048624855553)
              ·
                refine ⟨3898225849280286468641665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5197634465707048624855553 3898225849280286468641665)
                ·
                  refine ⟨2923669386960214851481249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898225849280286468641665 2923669386960214851481249)
                  ·
                    refine ⟨2192752040220161138610937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2923669386960214851481249 2192752040220161138610937)
                    ·
                      refine ⟨1644564030165120853958203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192752040220161138610937 1644564030165120853958203)
                      ·
                        rfl

theorem cell23_3202777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_3202777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202777 prefixEnd_3202777 := by exact prefixLift 3202777
  have htrace : WordTrace (prefixWord ++ tailWord_3202777) baseStart_3202777 baseEnd_3202777 := by
    simpa [prefixWord, tailWord_3202777, baseEnd_3202777] using wordTrace_append hprefix tailTrace_3202777
  have hstable : (prefixWord ++ tailWord_3202777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202777).length < 2 ^ (prefixWord ++ tailWord_3202777).sum := by decide
  have hdescent : baseEnd_3202777 < baseStart_3202777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202783 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 5]
def baseStart_3202783 : Nat := 118140960795 + 3202783 * 2 ^ 59
def prefixEnd_3202783 : Nat := 4983230072969 + 3 ^ 40 * 3202783 * 2
def baseEnd_3202783 : Nat := 182729679005449758942575

theorem tailTrace_3202783 : CollatzResearch.WordTrace tailWord_3202783 prefixEnd_3202783 182729679005449758942575 := by
  unfold tailWord_3202783
  simp only [CollatzResearch.WordTrace]
  refine ⟨116815092755871657633269003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77876728503914438422179335 116815092755871657633269003)
  ·
    refine ⟨175222639133807486449903505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116815092755871657633269003 175222639133807486449903505)
    ·
      refine ⟨131416979350355614837427629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175222639133807486449903505 131416979350355614837427629)
      ·
        refine ⟨49281367256383355564035361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131416979350355614837427629 49281367256383355564035361)
        ·
          refine ⟨36961025442287516673026521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49281367256383355564035361 36961025442287516673026521)
          ·
            refine ⟨27720769081715637504769891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36961025442287516673026521 27720769081715637504769891)
            ·
              refine ⟨41581153622573456257154837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27720769081715637504769891 41581153622573456257154837)
              ·
                refine ⟨1949116576058130762054133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41581153622573456257154837 1949116576058130762054133)
                ·
                  refine ⟨182729679005449758942575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1949116576058130762054133 182729679005449758942575)
                  ·
                    rfl

theorem cell23_3202783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 5].length) (baseStart_3202783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202783 prefixEnd_3202783 := by exact prefixLift 3202783
  have htrace : WordTrace (prefixWord ++ tailWord_3202783) baseStart_3202783 baseEnd_3202783 := by
    simpa [prefixWord, tailWord_3202783, baseEnd_3202783] using wordTrace_append hprefix tailTrace_3202783
  have hstable : (prefixWord ++ tailWord_3202783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202783).length < 2 ^ (prefixWord ++ tailWord_3202783).sum := by decide
  have hdescent : baseEnd_3202783 < baseStart_3202783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202796 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_3202796 : Nat := 118140960795 + 3202796 * 2 ^ 59
def prefixEnd_3202796 : Nat := 4983230072969 + 3 ^ 40 * 3202796 * 2
def baseEnd_3202796 : Nat := 548191262099185426540205

theorem tailTrace_3202796 : CollatzResearch.WordTrace tailWord_3202796 prefixEnd_3202796 548191262099185426540205 := by
  unfold tailWord_3202796
  simp only [CollatzResearch.WordTrace]
  refine ⟨58407783452412280426746121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77877044603216373902328161 58407783452412280426746121)
  ·
    refine ⟨43805837589309210320059591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58407783452412280426746121 43805837589309210320059591)
    ·
      refine ⟨65708756383963815480089387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43805837589309210320059591 65708756383963815480089387)
      ·
        refine ⟨98563134575945723220134081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65708756383963815480089387 98563134575945723220134081)
        ·
          refine ⟨73922350931959292415100561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98563134575945723220134081 73922350931959292415100561)
          ·
            refine ⟨55441763198969469311325421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73922350931959292415100561 55441763198969469311325421)
            ·
              refine ⟨20790661199613550991747033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55441763198969469311325421 20790661199613550991747033)
              ·
                refine ⟨15592995899710163243810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20790661199613550991747033 15592995899710163243810275)
                ·
                  refine ⟨23389493849565244865715413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15592995899710163243810275 23389493849565244865715413)
                  ·
                    refine ⟨548191262099185426540205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23389493849565244865715413 548191262099185426540205)
                    ·
                      rfl

theorem cell23_3202796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_3202796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202796 prefixEnd_3202796 := by exact prefixLift 3202796
  have htrace : WordTrace (prefixWord ++ tailWord_3202796) baseStart_3202796 baseEnd_3202796 := by
    simpa [prefixWord, tailWord_3202796, baseEnd_3202796] using wordTrace_append hprefix tailTrace_3202796
  have hstable : (prefixWord ++ tailWord_3202796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202796).length < 2 ^ (prefixWord ++ tailWord_3202796).sum := by decide
  have hdescent : baseEnd_3202796 < baseStart_3202796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202803 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 5, 2]
def baseStart_3202803 : Nat := 118140960795 + 3202803 * 2 ^ 59
def prefixEnd_3202803 : Nat := 4983230072969 + 3 ^ 40 * 3202803 * 2
def baseEnd_3202803 : Nat := 1644577380662137752233083

theorem tailTrace_3202803 : CollatzResearch.WordTrace tailWord_3202803 prefixEnd_3202803 1644577380662137752233083 := by
  unfold tailWord_3202803
  simp only [CollatzResearch.WordTrace]
  refine ⟨116815822215799201048997063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77877214810532800699331375 116815822215799201048997063)
  ·
    refine ⟨175223733323698801573495595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116815822215799201048997063 175223733323698801573495595)
    ·
      refine ⟨262835599985548202360243393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175223733323698801573495595 262835599985548202360243393)
      ·
        refine ⟨197126699989161151770182545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262835599985548202360243393 197126699989161151770182545)
        ·
          refine ⟨147845024991870863827636909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197126699989161151770182545 147845024991870863827636909)
          ·
            refine ⟨55441884371951573935363841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147845024991870863827636909 55441884371951573935363841)
            ·
              refine ⟨41581413278963680451522881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55441884371951573935363841 41581413278963680451522881)
              ·
                refine ⟨31186059959222760338642161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41581413278963680451522881 31186059959222760338642161)
                ·
                  refine ⟨23389544969417070253981621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31186059959222760338642161 23389544969417070253981621)
                  ·
                    refine ⟨2192769840882850336310777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23389544969417070253981621 2192769840882850336310777)
                    ·
                      refine ⟨1644577380662137752233083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192769840882850336310777 1644577380662137752233083)
                      ·
                        rfl

theorem cell23_3202803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5, 2].length) (baseStart_3202803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202803 prefixEnd_3202803 := by exact prefixLift 3202803
  have htrace : WordTrace (prefixWord ++ tailWord_3202803) baseStart_3202803 baseEnd_3202803 := by
    simpa [prefixWord, tailWord_3202803, baseEnd_3202803] using wordTrace_append hprefix tailTrace_3202803
  have hstable : (prefixWord ++ tailWord_3202803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202803).length < 2 ^ (prefixWord ++ tailWord_3202803).sum := by decide
  have hdescent : baseEnd_3202803 < baseStart_3202803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202834 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3202834 : Nat := 118140960795 + 3202834 * 2 ^ 59
def prefixEnd_3202834 : Nat := 4983230072969 + 3 ^ 40 * 3202834 * 2
def baseEnd_3202834 : Nat := 182732588729158570105049

theorem tailTrace_3202834 : CollatzResearch.WordTrace tailWord_3202834 prefixEnd_3202834 182732588729158570105049 := by
  unfold tailWord_3202834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29204238219671723335843889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77877968585791262228917037 29204238219671723335843889)
  ·
    refine ⟨21903178664753792501882917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29204238219671723335843889 21903178664753792501882917)
    ·
      refine ⟨4106845999641336094103047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21903178664753792501882917 4106845999641336094103047)
      ·
        refine ⟨6160268999462004141154571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106845999641336094103047 6160268999462004141154571)
        ·
          refine ⟨9240403499193006211731857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160268999462004141154571 9240403499193006211731857)
          ·
            refine ⟨6930302624394754658798893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9240403499193006211731857 6930302624394754658798893)
            ·
              refine ⟨2598863484148032997049585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6930302624394754658798893 2598863484148032997049585)
              ·
                refine ⟨1949147613111024747787189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2598863484148032997049585 1949147613111024747787189)
                ·
                  refine ⟨182732588729158570105049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1949147613111024747787189 182732588729158570105049)
                  ·
                    rfl

theorem cell23_3202834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3202834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202834 prefixEnd_3202834 := by exact prefixLift 3202834
  have htrace : WordTrace (prefixWord ++ tailWord_3202834) baseStart_3202834 baseEnd_3202834 := by
    simpa [prefixWord, tailWord_3202834, baseEnd_3202834] using wordTrace_append hprefix tailTrace_3202834
  have hstable : (prefixWord ++ tailWord_3202834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202834).length < 2 ^ (prefixWord ++ tailWord_3202834).sum := by decide
  have hdescent : baseEnd_3202834 < baseStart_3202834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202850 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_3202850 : Nat := 118140960795 + 3202850 * 2 ^ 59
def prefixEnd_3202850 : Nat := 4983230072969 + 3 ^ 40 * 3202850 * 2
def baseEnd_3202850 : Nat := 1644601514252899068345367

theorem tailTrace_3202850 : CollatzResearch.WordTrace tailWord_3202850 prefixEnd_3202850 1644601514252899068345367 := by
  unfold tailWord_3202850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29204384111657232018989501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77878357631085952050638669 29204384111657232018989501)
  ·
    refine ⟨10951644041871462007121063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29204384111657232018989501 10951644041871462007121063)
    ·
      refine ⟨16427466062807193010681595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10951644041871462007121063 16427466062807193010681595)
      ·
        refine ⟨24641199094210789516022393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16427466062807193010681595 24641199094210789516022393)
        ·
          refine ⟨18480899320658092137016795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24641199094210789516022393 18480899320658092137016795)
          ·
            refine ⟨27721348980987138205525193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18480899320658092137016795 27721348980987138205525193)
            ·
              refine ⟨20791011735740353654143895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27721348980987138205525193 20791011735740353654143895)
              ·
                refine ⟨31186517603610530481215843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20791011735740353654143895 31186517603610530481215843)
                ·
                  refine ⟨46779776405415795721823765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31186517603610530481215843 46779776405415795721823765)
                  ·
                    refine ⟨2192802019003865424460489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46779776405415795721823765 2192802019003865424460489)
                    ·
                      refine ⟨1644601514252899068345367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192802019003865424460489 1644601514252899068345367)
                      ·
                        rfl

theorem cell23_3202850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_3202850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202850 prefixEnd_3202850 := by exact prefixLift 3202850
  have htrace : WordTrace (prefixWord ++ tailWord_3202850) baseStart_3202850 baseEnd_3202850 := by
    simpa [prefixWord, tailWord_3202850, baseEnd_3202850] using wordTrace_append hprefix tailTrace_3202850
  have hstable : (prefixWord ++ tailWord_3202850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202850).length < 2 ^ (prefixWord ++ tailWord_3202850).sum := by decide
  have hdescent : baseEnd_3202850 < baseStart_3202850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202920 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3202920 : Nat := 118140960795 + 3202920 * 2 ^ 59
def prefixEnd_3202920 : Nat := 4983230072969 + 3 ^ 40 * 3202920 * 2
def baseEnd_3202920 : Nat := 548212485966237931490015

theorem tailTrace_3202920 : CollatzResearch.WordTrace tailWord_3202920 prefixEnd_3202920 548212485966237931490015 := by
  unfold tailWord_3202920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58410044778187665015503107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77880059704250220020670809 58410044778187665015503107)
  ·
    refine ⟨87615067167281497523254661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58410044778187665015503107 87615067167281497523254661)
    ·
      refine ⟨16427825093865280785610249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87615067167281497523254661 16427825093865280785610249)
      ·
        refine ⟨12320868820398960589207687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16427825093865280785610249 12320868820398960589207687)
        ·
          refine ⟨18481303230598440883811531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12320868820398960589207687 18481303230598440883811531)
          ·
            refine ⟨27721954845897661325717297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18481303230598440883811531 27721954845897661325717297)
            ·
              refine ⟨20791466134423245994287973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27721954845897661325717297 20791466134423245994287973)
              ·
                refine ⟨3898399900204358623928995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20791466134423245994287973 3898399900204358623928995)
                ·
                  refine ⟨5847599850306537935893493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898399900204358623928995 5847599850306537935893493)
                  ·
                    refine ⟨548212485966237931490015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5847599850306537935893493 548212485966237931490015)
                    ·
                      rfl

theorem cell23_3202920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3202920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202920 prefixEnd_3202920 := by exact prefixLift 3202920
  have htrace : WordTrace (prefixWord ++ tailWord_3202920) baseStart_3202920 baseEnd_3202920 := by
    simpa [prefixWord, tailWord_3202920, baseEnd_3202920] using wordTrace_append hprefix tailTrace_3202920
  have hstable : (prefixWord ++ tailWord_3202920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202920).length < 2 ^ (prefixWord ++ tailWord_3202920).sum := by decide
  have hdescent : baseEnd_3202920 < baseStart_3202920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202943 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_3202943 : Nat := 118140960795 + 3202943 * 2 ^ 59
def prefixEnd_3202943 : Nat := 4983230072969 + 3 ^ 40 * 3202943 * 2
def baseEnd_3202943 : Nat := 1644649267953767204482439

theorem tailTrace_3202943 : CollatzResearch.WordTrace tailWord_3202943 prefixEnd_3202943 1644649267953767204482439 := by
  unfold tailWord_3202943
  simp only [CollatzResearch.WordTrace]
  refine ⟨116820928435292004959093483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77880618956861336639395655 116820928435292004959093483)
  ·
    refine ⟨175231392652938007438640225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116820928435292004959093483 175231392652938007438640225)
    ·
      refine ⟨131423544489703505578980169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175231392652938007438640225 131423544489703505578980169)
      ·
        refine ⟨98567658367277629184235127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131423544489703505578980169 98567658367277629184235127)
        ·
          refine ⟨147851487550916443776352691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98567658367277629184235127 147851487550916443776352691)
          ·
            refine ⟨221777231326374665664529037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147851487550916443776352691 221777231326374665664529037)
            ·
              refine ⟨83166461747390499624198389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221777231326374665664529037 83166461747390499624198389)
              ·
                refine ⟨7796855788817859339768599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83166461747390499624198389 7796855788817859339768599)
                ·
                  refine ⟨11695283683226789009652899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7796855788817859339768599 11695283683226789009652899)
                  ·
                    refine ⟨17542925524840183514479349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11695283683226789009652899 17542925524840183514479349)
                    ·
                      refine ⟨1644649267953767204482439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17542925524840183514479349 1644649267953767204482439)
                      ·
                        rfl

theorem cell23_3202943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_3202943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202943 prefixEnd_3202943 := by exact prefixLift 3202943
  have htrace : WordTrace (prefixWord ++ tailWord_3202943) baseStart_3202943 baseEnd_3202943 := by
    simpa [prefixWord, tailWord_3202943, baseEnd_3202943] using wordTrace_append hprefix tailTrace_3202943
  have hstable : (prefixWord ++ tailWord_3202943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202943).length < 2 ^ (prefixWord ++ tailWord_3202943).sum := by decide
  have hdescent : baseEnd_3202943 < baseStart_3202943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202953 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_3202953 : Nat := 118140960795 + 3202953 * 2 ^ 59
def prefixEnd_3202953 : Nat := 4983230072969 + 3 ^ 40 * 3202953 * 2
def baseEnd_3202953 : Nat := 1644654402760312165357393

theorem tailTrace_3202953 : CollatzResearch.WordTrace tailWord_3202953 prefixEnd_3202953 1644654402760312165357393 := by
  unfold tailWord_3202953
  simp only [CollatzResearch.WordTrace]
  refine ⟨116821293165255776666957513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77880862110170517777971675 116821293165255776666957513)
  ·
    refine ⟨87615969873941832500218135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116821293165255776666957513 87615969873941832500218135)
    ·
      refine ⟨131423954810912748750327203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87615969873941832500218135 131423954810912748750327203)
      ·
        refine ⟨197135932216369123125490805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131423954810912748750327203 197135932216369123125490805)
        ·
          refine ⟨18481493645284605293014763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197135932216369123125490805 18481493645284605293014763)
          ·
            refine ⟨27722240467926907939522145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18481493645284605293014763 27722240467926907939522145)
            ·
              refine ⟨20791680350945180954641609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27722240467926907939522145 20791680350945180954641609)
              ·
                refine ⟨15593760263208885715981207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20791680350945180954641609 15593760263208885715981207)
                ·
                  refine ⟨23390640394813328573971811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15593760263208885715981207 23390640394813328573971811)
                  ·
                    refine ⟨35085960592219992860957717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23390640394813328573971811 35085960592219992860957717)
                    ·
                      refine ⟨1644654402760312165357393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35085960592219992860957717 1644654402760312165357393)
                      ·
                        rfl

theorem cell23_3202953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_3202953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202953 prefixEnd_3202953 := by exact prefixLift 3202953
  have htrace : WordTrace (prefixWord ++ tailWord_3202953) baseStart_3202953 baseEnd_3202953 := by
    simpa [prefixWord, tailWord_3202953, baseEnd_3202953] using wordTrace_append hprefix tailTrace_3202953
  have hstable : (prefixWord ++ tailWord_3202953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202953).length < 2 ^ (prefixWord ++ tailWord_3202953).sum := by decide
  have hdescent : baseEnd_3202953 < baseStart_3202953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202970 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3202970 : Nat := 118140960795 + 3202970 * 2 ^ 59
def prefixEnd_3202970 : Nat := 4983230072969 + 3 ^ 40 * 3202970 * 2
def baseEnd_3202970 : Nat := 1644663131931438598844815

theorem tailTrace_3202970 : CollatzResearch.WordTrace tailWord_3202970 prefixEnd_3202970 1644663131931438598844815 := by
  unfold tailWord_3202970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29205478301548547142581591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77881275470796125713550909 29205478301548547142581591)
  ·
    refine ⟨43808217452322820713872387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29205478301548547142581591 43808217452322820713872387)
    ·
      refine ⟨65712326178484231070808581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43808217452322820713872387 65712326178484231070808581)
      ·
        refine ⟨12321061158465793325776609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65712326178484231070808581 12321061158465793325776609)
        ·
          refine ⟨9240795868849344994332457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12321061158465793325776609 9240795868849344994332457)
          ·
            refine ⟨6930596901637008745749343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9240795868849344994332457 6930596901637008745749343)
            ·
              refine ⟨10395895352455513118624015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930596901637008745749343 10395895352455513118624015)
              ·
                refine ⟨15593843028683269677936023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10395895352455513118624015 15593843028683269677936023)
                ·
                  refine ⟨23390764543024904516904035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15593843028683269677936023 23390764543024904516904035)
                  ·
                    refine ⟨35086146814537356775356053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23390764543024904516904035 35086146814537356775356053)
                    ·
                      refine ⟨1644663131931438598844815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35086146814537356775356053 1644663131931438598844815)
                      ·
                        rfl

theorem cell23_3202970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3202970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202970 prefixEnd_3202970 := by exact prefixLift 3202970
  have htrace : WordTrace (prefixWord ++ tailWord_3202970) baseStart_3202970 baseEnd_3202970 := by
    simpa [prefixWord, tailWord_3202970, baseEnd_3202970] using wordTrace_append hprefix tailTrace_3202970
  have hstable : (prefixWord ++ tailWord_3202970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202970).length < 2 ^ (prefixWord ++ tailWord_3202970).sum := by decide
  have hdescent : baseEnd_3202970 < baseStart_3202970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202980 : List Nat := [2, 3, 1, 2, 1, 3, 4, 7]
def baseStart_3202980 : Nat := 118140960795 + 3202980 * 2 ^ 59
def prefixEnd_3202980 : Nat := 4983230072969 + 3 ^ 40 * 3202980 * 2
def baseEnd_3202980 : Nat := 60913639508814205915547

theorem tailTrace_3202980 : CollatzResearch.WordTrace tailWord_3202980 prefixEnd_3202980 60913639508814205915547 := by
  unfold tailWord_3202980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58411138968078980139095197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77881518624105306852126929 58411138968078980139095197)
  ·
    refine ⟨21904177113029617552160699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58411138968078980139095197 21904177113029617552160699)
    ·
      refine ⟨32856265669544426328241049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21904177113029617552160699 32856265669544426328241049)
      ·
        refine ⟨24642199252158319746180787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32856265669544426328241049 24642199252158319746180787)
        ·
          refine ⟨36963298878237479619271181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24642199252158319746180787 36963298878237479619271181)
          ·
            refine ⟨13861237079339054857226693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36963298878237479619271181 13861237079339054857226693)
            ·
              refine ⟨2598981952376072785730005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13861237079339054857226693 2598981952376072785730005)
              ·
                refine ⟨60913639508814205915547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2598981952376072785730005 60913639508814205915547)
                ·
                  rfl

theorem cell23_3202980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 7].length) (baseStart_3202980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3202980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3202980 prefixEnd_3202980 := by exact prefixLift 3202980
  have htrace : WordTrace (prefixWord ++ tailWord_3202980) baseStart_3202980 baseEnd_3202980 := by
    simpa [prefixWord, tailWord_3202980, baseEnd_3202980] using wordTrace_append hprefix tailTrace_3202980
  have hstable : (prefixWord ++ tailWord_3202980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202980).length < 2 ^ (prefixWord ++ tailWord_3202980).sum := by decide
  have hdescent : baseEnd_3202980 < baseStart_3202980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203007 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 3]
def baseStart_3203007 : Nat := 118140960795 + 3203007 * 2 ^ 59
def prefixEnd_3203007 : Nat := 4983230072969 + 3 ^ 40 * 3203007 * 2
def baseEnd_3203007 : Nat := 1644682130715654954082145

theorem tailTrace_3203007 : CollatzResearch.WordTrace tailWord_3203007 prefixEnd_3203007 1644682130715654954082145 := by
  unfold tailWord_3203007
  simp only [CollatzResearch.WordTrace]
  refine ⟨116823262707060143889423275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77882175138040095926282183 116823262707060143889423275)
  ·
    refine ⟨175234894060590215834134913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116823262707060143889423275 175234894060590215834134913)
    ·
      refine ⟨131426170545442661875601185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175234894060590215834134913 131426170545442661875601185)
      ·
        refine ⟨98569627909081996406700889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131426170545442661875601185 98569627909081996406700889)
        ·
          refine ⟨73927220931811497305025667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98569627909081996406700889 73927220931811497305025667)
          ·
            refine ⟨110890831397717245957538501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73927220931811497305025667 110890831397717245957538501)
            ·
              refine ⟨20792030887071983617038469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110890831397717245957538501 20792030887071983617038469)
              ·
                refine ⟨3898505791325996928194713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20792030887071983617038469 3898505791325996928194713)
                ·
                  refine ⟨2923879343494497696146035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898505791325996928194713 2923879343494497696146035)
                  ·
                    refine ⟨4385819015241746544219053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923879343494497696146035 4385819015241746544219053)
                    ·
                      refine ⟨1644682130715654954082145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385819015241746544219053 1644682130715654954082145)
                      ·
                        rfl

theorem cell23_3203007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_3203007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203007 prefixEnd_3203007 := by exact prefixLift 3203007
  have htrace : WordTrace (prefixWord ++ tailWord_3203007) baseStart_3203007 baseEnd_3203007 := by
    simpa [prefixWord, tailWord_3203007, baseEnd_3203007] using wordTrace_append hprefix tailTrace_3203007
  have hstable : (prefixWord ++ tailWord_3203007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203007).length < 2 ^ (prefixWord ++ tailWord_3203007).sum := by decide
  have hdescent : baseEnd_3203007 < baseStart_3203007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203023 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 8]
def baseStart_3203023 : Nat := 118140960795 + 3203023 * 2 ^ 59
def prefixEnd_3203023 : Nat := 4983230072969 + 3 ^ 40 * 3203023 * 2
def baseEnd_3203023 : Nat := 548230115468708963827357

theorem tailTrace_3203023 : CollatzResearch.WordTrace tailWord_3203023 prefixEnd_3203023 548230115468708963827357 := by
  unfold tailWord_3203023
  simp only [CollatzResearch.WordTrace]
  refine ⟨116823846275002178622005723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77882564183334785748003815 116823846275002178622005723)
  ·
    refine ⟨175235769412503267933008585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116823846275002178622005723 175235769412503267933008585)
    ·
      refine ⟨131426827059377450949756439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175235769412503267933008585 131426827059377450949756439)
      ·
        refine ⟨197140240589066176424634659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131426827059377450949756439 197140240589066176424634659)
        ·
          refine ⟨295710360883599264636951989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197140240589066176424634659 295710360883599264636951989)
          ·
            refine ⟨27722846332837431059714249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295710360883599264636951989 27722846332837431059714249)
            ·
              refine ⟨20792134749628073294785687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27722846332837431059714249 20792134749628073294785687)
              ·
                refine ⟨31188202124442109942178531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20792134749628073294785687 31188202124442109942178531)
                ·
                  refine ⟨46782303186663164913267797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31188202124442109942178531 46782303186663164913267797)
                  ·
                    refine ⟨548230115468708963827357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46782303186663164913267797 548230115468708963827357)
                    ·
                      rfl

theorem cell23_3203023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_3203023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203023 prefixEnd_3203023 := by exact prefixLift 3203023
  have htrace : WordTrace (prefixWord ++ tailWord_3203023) baseStart_3203023 baseEnd_3203023 := by
    simpa [prefixWord, tailWord_3203023, baseEnd_3203023] using wordTrace_append hprefix tailTrace_3203023
  have hstable : (prefixWord ++ tailWord_3203023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203023).length < 2 ^ (prefixWord ++ tailWord_3203023).sum := by decide
  have hdescent : baseEnd_3203023 < baseStart_3203023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203024 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3]
def baseStart_3203024 : Nat := 118140960795 + 3203024 * 2 ^ 59
def prefixEnd_3203024 : Nat := 4983230072969 + 3 ^ 40 * 3203024 * 2
def baseEnd_3203024 : Nat := 1644690859886781387569567

theorem tailTrace_3203024 : CollatzResearch.WordTrace tailWord_3203024 prefixEnd_3203024 1644690859886781387569567 := by
  unfold tailWord_3203024
  simp only [CollatzResearch.WordTrace]
  refine ⟨58411941373999277896396063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77882588498665703861861417 58411941373999277896396063)
  ·
    refine ⟨87617912060998916844594095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58411941373999277896396063 87617912060998916844594095)
    ·
      refine ⟨131426868091498375266891143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87617912060998916844594095 131426868091498375266891143)
      ·
        refine ⟨197140302137247562900336715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131426868091498375266891143 197140302137247562900336715)
        ·
          refine ⟨295710453205871344350505073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197140302137247562900336715 295710453205871344350505073)
          ·
            refine ⟨221782839904403508262878805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295710453205871344350505073 221782839904403508262878805)
            ·
              refine ⟨2599017655129728612455611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 221782839904403508262878805 2599017655129728612455611)
              ·
                refine ⟨3898526482694592918683417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599017655129728612455611 3898526482694592918683417)
                ·
                  refine ⟨2923894862020944689012563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898526482694592918683417 2923894862020944689012563)
                  ·
                    refine ⟨4385842293031417033518845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923894862020944689012563 4385842293031417033518845)
                    ·
                      refine ⟨1644690859886781387569567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4385842293031417033518845 1644690859886781387569567)
                      ·
                        rfl

theorem cell23_3203024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 2, 1, 3].length) (baseStart_3203024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203024 prefixEnd_3203024 := by exact prefixLift 3203024
  have htrace : WordTrace (prefixWord ++ tailWord_3203024) baseStart_3203024 baseEnd_3203024 := by
    simpa [prefixWord, tailWord_3203024, baseEnd_3203024] using wordTrace_append hprefix tailTrace_3203024
  have hstable : (prefixWord ++ tailWord_3203024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203024).length < 2 ^ (prefixWord ++ tailWord_3203024).sum := by decide
  have hdescent : baseEnd_3203024 < baseStart_3203024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203034 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2]
def baseStart_3203034 : Nat := 118140960795 + 3203034 * 2 ^ 59
def prefixEnd_3203034 : Nat := 4983230072969 + 3 ^ 40 * 3203034 * 2
def baseEnd_3203034 : Nat := 1644695994693326348444521

theorem tailTrace_3203034 : CollatzResearch.WordTrace tailWord_3203034 prefixEnd_3203034 1644695994693326348444521 := by
  unfold tailWord_3203034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29206061869490581875164039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77882831651974885000437437 29206061869490581875164039)
  ·
    refine ⟨43809092804235872812746059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29206061869490581875164039 43809092804235872812746059)
    ·
      refine ⟨65713639206353809219119089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43809092804235872812746059 65713639206353809219119089)
      ·
        refine ⟨49285229404765356914339317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65713639206353809219119089 49285229404765356914339317)
        ·
          refine ⟨4620490256696752210719311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49285229404765356914339317 4620490256696752210719311)
          ·
            refine ⟨6930735385045128316078967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620490256696752210719311 6930735385045128316078967)
            ·
              refine ⟨10396103077567692474118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930735385045128316078967 10396103077567692474118451)
              ·
                refine ⟨15594154616351538711177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396103077567692474118451 15594154616351538711177677)
                ·
                  refine ⟨5847807981131827016691629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15594154616351538711177677 5847807981131827016691629)
                  ·
                    refine ⟨2192927992924435131259361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5847807981131827016691629 2192927992924435131259361)
                    ·
                      refine ⟨1644695994693326348444521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192927992924435131259361 1644695994693326348444521)
                      ·
                        rfl

theorem cell23_3203034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_3203034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203034 prefixEnd_3203034 := by exact prefixLift 3203034
  have htrace : WordTrace (prefixWord ++ tailWord_3203034) baseStart_3203034 baseEnd_3203034 := by
    simpa [prefixWord, tailWord_3203034, baseEnd_3203034] using wordTrace_append hprefix tailTrace_3203034
  have hstable : (prefixWord ++ tailWord_3203034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203034).length < 2 ^ (prefixWord ++ tailWord_3203034).sum := by decide
  have hdescent : baseEnd_3203034 < baseStart_3203034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203050 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3203050 : Nat := 118140960795 + 3203050 * 2 ^ 59
def prefixEnd_3203050 : Nat := 4983230072969 + 3 ^ 40 * 3203050 * 2
def baseEnd_3203050 : Nat := 1644704210383798285844447

theorem tailTrace_3203050 : CollatzResearch.WordTrace tailWord_3203050 prefixEnd_3203050 1644704210383798285844447 := by
  unfold tailWord_3203050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29206207761476090558309651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77883220697269574822159069 29206207761476090558309651)
  ·
    refine ⟨43809311642214135837464477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29206207761476090558309651 43809311642214135837464477)
    ·
      refine ⟨16428491865830300939049179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43809311642214135837464477 16428491865830300939049179)
      ·
        refine ⟨24642737798745451408573769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16428491865830300939049179 24642737798745451408573769)
        ·
          refine ⟨18482053349059088556430327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24642737798745451408573769 18482053349059088556430327)
          ·
            refine ⟨27723080023588632834645491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18482053349059088556430327 27723080023588632834645491)
            ·
              refine ⟨41584620035382949251968237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27723080023588632834645491 41584620035382949251968237)
              ·
                refine ⟨15594232513268605969488089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41584620035382949251968237 15594232513268605969488089)
                ·
                  refine ⟨11695674384951454477116067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15594232513268605969488089 11695674384951454477116067)
                  ·
                    refine ⟨17543511577427181715674101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11695674384951454477116067 17543511577427181715674101)
                    ·
                      refine ⟨1644704210383798285844447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17543511577427181715674101 1644704210383798285844447)
                      ·
                        rfl

theorem cell23_3203050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3203050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203050 prefixEnd_3203050 := by exact prefixLift 3203050
  have htrace : WordTrace (prefixWord ++ tailWord_3203050) baseStart_3203050 baseEnd_3203050 := by
    simpa [prefixWord, tailWord_3203050, baseEnd_3203050] using wordTrace_append hprefix tailTrace_3203050
  have hstable : (prefixWord ++ tailWord_3203050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203050).length < 2 ^ (prefixWord ++ tailWord_3203050).sum := by decide
  have hdescent : baseEnd_3203050 < baseStart_3203050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203064 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_3203064 : Nat := 118140960795 + 3203064 * 2 ^ 59
def prefixEnd_3203064 : Nat := 4983230072969 + 3 ^ 40 * 3203064 * 2
def baseEnd_3203064 : Nat := 1644711399112961231069383

theorem tailTrace_3203064 : CollatzResearch.WordTrace tailWord_3203064 prefixEnd_3203064 1644711399112961231069383 := by
  unfold tailWord_3203064
  simp only [CollatzResearch.WordTrace]
  refine ⟨58412670833926821312124123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77883561111902428416165497 58412670833926821312124123)
  ·
    refine ⟨87619006250890231968186185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58412670833926821312124123 87619006250890231968186185)
    ·
      refine ⟨65714254688167673976139639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87619006250890231968186185 65714254688167673976139639)
      ·
        refine ⟨98571382032251510964209459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65714254688167673976139639 98571382032251510964209459)
        ·
          refine ⟨147857073048377266446314189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98571382032251510964209459 147857073048377266446314189)
          ·
            refine ⟨55446402393141474917367821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147857073048377266446314189 55446402393141474917367821)
            ·
              refine ⟨20792400897428053094012933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55446402393141474917367821 20792400897428053094012933)
              ·
                refine ⟨3898575168267759955127425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20792400897428053094012933 3898575168267759955127425)
                ·
                  refine ⟨2923931376200819966345569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898575168267759955127425 2923931376200819966345569)
                  ·
                    refine ⟨2192948532150614974759177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2923931376200819966345569 2192948532150614974759177)
                    ·
                      refine ⟨1644711399112961231069383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2192948532150614974759177 1644711399112961231069383)
                      ·
                        rfl

theorem cell23_3203064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_3203064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203064 prefixEnd_3203064 := by exact prefixLift 3203064
  have htrace : WordTrace (prefixWord ++ tailWord_3203064) baseStart_3203064 baseEnd_3203064 := by
    simpa [prefixWord, tailWord_3203064, baseEnd_3203064] using wordTrace_append hprefix tailTrace_3203064
  have hstable : (prefixWord ++ tailWord_3203064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203064).length < 2 ^ (prefixWord ++ tailWord_3203064).sum := by decide
  have hdescent : baseEnd_3203064 < baseStart_3203064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203137 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3203137 : Nat := 118140960795 + 3203137 * 2 ^ 59
def prefixEnd_3203137 : Nat := 4983230072969 + 3 ^ 40 * 3203137 * 2
def baseEnd_3203137 : Nat := 1644748883200739445456547

theorem tailTrace_3203137 : CollatzResearch.WordTrace tailWord_3203137 prefixEnd_3203137 1644748883200739445456547 := by
  unfold tailWord_3203137
  simp only [CollatzResearch.WordTrace]
  refine ⟨116828004196589176091655665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77885336131059450727770443 116828004196589176091655665)
  ·
    refine ⟨87621003147441882068741749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116828004196589176091655665 87621003147441882068741749)
    ·
      refine ⟨8214469045072676443944539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87621003147441882068741749 8214469045072676443944539)
      ·
        refine ⟨12321703567609014665916809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8214469045072676443944539 12321703567609014665916809)
        ·
          refine ⟨9241277675706760999437607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12321703567609014665916809 9241277675706760999437607)
          ·
            refine ⟨13861916513560141499156411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241277675706760999437607 13861916513560141499156411)
            ·
              refine ⟨20792874770340212248734617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13861916513560141499156411 20792874770340212248734617)
              ·
                refine ⟨15594656077755159186550963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20792874770340212248734617 15594656077755159186550963)
                ·
                  refine ⟨23391984116632738779826445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15594656077755159186550963 23391984116632738779826445)
                  ·
                    refine ⟨8771994043737277042434917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23391984116632738779826445 8771994043737277042434917)
                    ·
                      refine ⟨1644748883200739445456547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8771994043737277042434917 1644748883200739445456547)
                      ·
                        rfl

theorem cell23_3203137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3203137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203137 prefixEnd_3203137 := by exact prefixLift 3203137
  have htrace : WordTrace (prefixWord ++ tailWord_3203137) baseStart_3203137 baseEnd_3203137 := by
    simpa [prefixWord, tailWord_3203137, baseEnd_3203137] using wordTrace_append hprefix tailTrace_3203137
  have hstable : (prefixWord ++ tailWord_3203137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203137).length < 2 ^ (prefixWord ++ tailWord_3203137).sum := by decide
  have hdescent : baseEnd_3203137 < baseStart_3203137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203157 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3203157 : Nat := 118140960795 + 3203157 * 2 ^ 59
def prefixEnd_3203157 : Nat := 4983230072969 + 3 ^ 40 * 3203157 * 2
def baseEnd_3203157 : Nat := 1644759152813829367206455

theorem tailTrace_3203157 : CollatzResearch.WordTrace tailWord_3203157 prefixEnd_3203157 1644759152813829367206455 := by
  unfold tailWord_3203157
  simp only [CollatzResearch.WordTrace]
  refine ⟨116828733656516719507383725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77885822437677813004922483 116828733656516719507383725)
  ·
    refine ⟨43810775121193769815268897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116828733656516719507383725 43810775121193769815268897)
    ·
      refine ⟨32858081340895327361451673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43810775121193769815268897 32858081340895327361451673)
      ·
        refine ⟨24643561005671495521088755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32858081340895327361451673 24643561005671495521088755)
        ·
          refine ⟨36965341508507243281633133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24643561005671495521088755 36965341508507243281633133)
          ·
            refine ⟨13862003065690216230612425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36965341508507243281633133 13862003065690216230612425)
            ·
              refine ⟨10396502299267662172959319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862003065690216230612425 10396502299267662172959319)
              ·
                refine ⟨15594753448901493259438979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396502299267662172959319 15594753448901493259438979)
                ·
                  refine ⟨23392130173352239889158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15594753448901493259438979 23392130173352239889158469)
                  ·
                    refine ⟨4386024407503544979217213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23392130173352239889158469 4386024407503544979217213)
                    ·
                      refine ⟨1644759152813829367206455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386024407503544979217213 1644759152813829367206455)
                      ·
                        rfl

theorem cell23_3203157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3203157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203157 prefixEnd_3203157 := by exact prefixLift 3203157
  have htrace : WordTrace (prefixWord ++ tailWord_3203157) baseStart_3203157 baseEnd_3203157 := by
    simpa [prefixWord, tailWord_3203157, baseEnd_3203157] using wordTrace_append hprefix tailTrace_3203157
  have hstable : (prefixWord ++ tailWord_3203157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203157).length < 2 ^ (prefixWord ++ tailWord_3203157).sum := by decide
  have hdescent : baseEnd_3203157 < baseStart_3203157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203160 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 8]
def baseStart_3203160 : Nat := 118140960795 + 3203160 * 2 ^ 59
def prefixEnd_3203160 : Nat := 4983230072969 + 3 ^ 40 * 3203160 * 2
def baseEnd_3203160 : Nat := 182751188139532539496549

theorem tailTrace_3203160 : CollatzResearch.WordTrace tailWord_3203160 prefixEnd_3203160 182751188139532539496549 := by
  unfold tailWord_3203160
  simp only [CollatzResearch.WordTrace]
  refine ⟨58414421537752925509871467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77885895383670567346495289 58414421537752925509871467)
  ·
    refine ⟨87621632306629388264807201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58414421537752925509871467 87621632306629388264807201)
    ·
      refine ⟨65716224229972041198605401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87621632306629388264807201 65716224229972041198605401)
      ·
        refine ⟨49287168172479030898954051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65716224229972041198605401 49287168172479030898954051)
        ·
          refine ⟨73930752258718546348431077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49287168172479030898954051 73930752258718546348431077)
          ·
            refine ⟨13862016048509727440330827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73930752258718546348431077 13862016048509727440330827)
            ·
              refine ⟨20793024072764591160496241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13862016048509727440330827 20793024072764591160496241)
              ·
                refine ⟨15594768054573443370372181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20793024072764591160496241 15594768054573443370372181)
                ·
                  refine ⟨182751188139532539496549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15594768054573443370372181 182751188139532539496549)
                  ·
                    rfl

theorem cell23_3203160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_3203160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203160 prefixEnd_3203160 := by exact prefixLift 3203160
  have htrace : WordTrace (prefixWord ++ tailWord_3203160) baseStart_3203160 baseEnd_3203160 := by
    simpa [prefixWord, tailWord_3203160, baseEnd_3203160] using wordTrace_append hprefix tailTrace_3203160
  have hstable : (prefixWord ++ tailWord_3203160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203160).length < 2 ^ (prefixWord ++ tailWord_3203160).sum := by decide
  have hdescent : baseEnd_3203160 < baseStart_3203160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203204 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3203204 : Nat := 118140960795 + 3203204 * 2 ^ 59
def prefixEnd_3203204 : Nat := 4983230072969 + 3 ^ 40 * 3203204 * 2
def baseEnd_3203204 : Nat := 1644783286404590683318739

theorem tailTrace_3203204 : CollatzResearch.WordTrace tailWord_3203204 prefixEnd_3203204 1644783286404590683318739 := by
  unfold tailWord_3203204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58415223943673223267172333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77886965258230964356229777 58415223943673223267172333)
  ·
    refine ⟨21905708978877458725189625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58415223943673223267172333 21905708978877458725189625)
    ·
      refine ⟨16429281734158094043892219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21905708978877458725189625 16429281734158094043892219)
      ·
        refine ⟨24643922601237141065838329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16429281734158094043892219 24643922601237141065838329)
        ·
          refine ⟨18482941950927855799378747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24643922601237141065838329 18482941950927855799378747)
          ·
            refine ⟨27724412926391783699068121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18482941950927855799378747 27724412926391783699068121)
            ·
              refine ⟨20793309694793837774301091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27724412926391783699068121 20793309694793837774301091)
              ·
                refine ⟨31189964542190756661451637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20793309694793837774301091 31189964542190756661451637)
                ·
                  refine ⟨2924059175830383437011091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31189964542190756661451637 2924059175830383437011091)
                  ·
                    refine ⟨4386088763745575155516637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2924059175830383437011091 4386088763745575155516637)
                    ·
                      refine ⟨1644783286404590683318739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386088763745575155516637 1644783286404590683318739)
                      ·
                        rfl

theorem cell23_3203204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3203204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203204 prefixEnd_3203204 := by exact prefixLift 3203204
  have htrace : WordTrace (prefixWord ++ tailWord_3203204) baseStart_3203204 baseEnd_3203204 := by
    simpa [prefixWord, tailWord_3203204, baseEnd_3203204] using wordTrace_append hprefix tailTrace_3203204
  have hstable : (prefixWord ++ tailWord_3203204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203204).length < 2 ^ (prefixWord ++ tailWord_3203204).sum := by decide
  have hdescent : baseEnd_3203204 < baseStart_3203204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203221 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_3203221 : Nat := 118140960795 + 3203221 * 2 ^ 59
def prefixEnd_3203221 : Nat := 4983230072969 + 3 ^ 40 * 3203221 * 2
def baseEnd_3203221 : Nat := 1644792015575717116806161

theorem tailTrace_3203221 : CollatzResearch.WordTrace tailWord_3203221 prefixEnd_3203221 1644792015575717116806161 := by
  unfold tailWord_3203221
  simp only [CollatzResearch.WordTrace]
  refine ⟨116831067928284858437713517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77887378618856572291809011 116831067928284858437713517)
  ·
    refine ⟨43811650473106821914142569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116831067928284858437713517 43811650473106821914142569)
    ·
      refine ⟨32858737854830116435606927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43811650473106821914142569 32858737854830116435606927)
      ·
        refine ⟨49288106782245174653410391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32858737854830116435606927 49288106782245174653410391)
        ·
          refine ⟨73932160173367761980115587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49288106782245174653410391 73932160173367761980115587)
          ·
            refine ⟨110898240260051642970173381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73932160173367761980115587 110898240260051642970173381)
            ·
              refine ⟨20793420048759683056907509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110898240260051642970173381 20793420048759683056907509)
              ·
                refine ⟨1949383129571220286585079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20793420048759683056907509 1949383129571220286585079)
                ·
                  refine ⟨2924074694356830429877619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949383129571220286585079 2924074694356830429877619)
                  ·
                    refine ⟨4386112041535245644816429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2924074694356830429877619 4386112041535245644816429)
                    ·
                      refine ⟨1644792015575717116806161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386112041535245644816429 1644792015575717116806161)
                      ·
                        rfl

theorem cell23_3203221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_3203221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203221 prefixEnd_3203221 := by exact prefixLift 3203221
  have htrace : WordTrace (prefixWord ++ tailWord_3203221) baseStart_3203221 baseEnd_3203221 := by
    simpa [prefixWord, tailWord_3203221, baseEnd_3203221] using wordTrace_append hprefix tailTrace_3203221
  have hstable : (prefixWord ++ tailWord_3203221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203221).length < 2 ^ (prefixWord ++ tailWord_3203221).sum := by decide
  have hdescent : baseEnd_3203221 < baseStart_3203221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203227 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 8, 2]
def baseStart_3203227 : Nat := 118140960795 + 3203227 * 2 ^ 59
def prefixEnd_3203227 : Nat := 4983230072969 + 3 ^ 40 * 3203227 * 2
def baseEnd_3203227 : Nat := 1644795096459644093331133

theorem tailTrace_3203227 : CollatzResearch.WordTrace tailWord_3203227 prefixEnd_3203227 1644795096459644093331133 := by
  unfold tailWord_3203227
  simp only [CollatzResearch.WordTrace]
  refine ⟨116831286766263121462431935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77887524510842080974954623 116831286766263121462431935)
  ·
    refine ⟨175246930149394682193647903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116831286766263121462431935 175246930149394682193647903)
    ·
      refine ⟨262870395224092023290471855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175246930149394682193647903 262870395224092023290471855)
      ·
        refine ⟨394305592836138034935707783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262870395224092023290471855 394305592836138034935707783)
        ·
          refine ⟨591458389254207052403561675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394305592836138034935707783 591458389254207052403561675)
          ·
            refine ⟨887187583881310578605342513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591458389254207052403561675 887187583881310578605342513)
            ·
              refine ⟨665390687910982933954006885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887187583881310578605342513 665390687910982933954006885)
              ·
                refine ⟨124760753983309300116376291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665390687910982933954006885 124760753983309300116376291)
                ·
                  refine ⟨187141130974963950174564437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124760753983309300116376291 187141130974963950174564437)
                  ·
                    refine ⟨2193060128612858791108177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 187141130974963950174564437 2193060128612858791108177)
                    ·
                      refine ⟨1644795096459644093331133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193060128612858791108177 1644795096459644093331133)
                      ·
                        rfl

theorem cell23_3203227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8, 2].length) (baseStart_3203227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203227 prefixEnd_3203227 := by exact prefixLift 3203227
  have htrace : WordTrace (prefixWord ++ tailWord_3203227) baseStart_3203227 baseEnd_3203227 := by
    simpa [prefixWord, tailWord_3203227, baseEnd_3203227] using wordTrace_append hprefix tailTrace_3203227
  have hstable : (prefixWord ++ tailWord_3203227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203227).length < 2 ^ (prefixWord ++ tailWord_3203227).sum := by decide
  have hdescent : baseEnd_3203227 < baseStart_3203227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203231 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3203231 : Nat := 118140960795 + 3203231 * 2 ^ 59
def prefixEnd_3203231 : Nat := 4983230072969 + 3 ^ 40 * 3203231 * 2
def baseEnd_3203231 : Nat := 1644797150382262077681115

theorem tailTrace_3203231 : CollatzResearch.WordTrace tailWord_3203231 prefixEnd_3203231 1644797150382262077681115 := by
  unfold tailWord_3203231
  simp only [CollatzResearch.WordTrace]
  refine ⟨116831432658248630145577547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77887621772165753430385031 116831432658248630145577547)
  ·
    refine ⟨175247148987372945218366321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116831432658248630145577547 175247148987372945218366321)
    ·
      refine ⟨131435361740529708913774741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175247148987372945218366321 131435361740529708913774741)
      ·
        refine ⟨6161032581587330105333191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131435361740529708913774741 6161032581587330105333191)
        ·
          refine ⟨9241548872380995157999787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161032581587330105333191 9241548872380995157999787)
          ·
            refine ⟨13862323308571492736999681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241548872380995157999787 13862323308571492736999681)
            ·
              refine ⟨10396742481428619552749761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862323308571492736999681 10396742481428619552749761)
              ·
                refine ⟨7797556861071464664562321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396742481428619552749761 7797556861071464664562321)
                ·
                  refine ⟨5848167645803598498421741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797556861071464664562321 5848167645803598498421741)
                  ·
                    refine ⟨2193062867176349436908153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5848167645803598498421741 2193062867176349436908153)
                    ·
                      refine ⟨1644797150382262077681115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193062867176349436908153 1644797150382262077681115)
                      ·
                        rfl

theorem cell23_3203231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3203231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203231 prefixEnd_3203231 := by exact prefixLift 3203231
  have htrace : WordTrace (prefixWord ++ tailWord_3203231) baseStart_3203231 baseEnd_3203231 := by
    simpa [prefixWord, tailWord_3203231, baseEnd_3203231] using wordTrace_append hprefix tailTrace_3203231
  have hstable : (prefixWord ++ tailWord_3203231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203231).length < 2 ^ (prefixWord ++ tailWord_3203231).sum := by decide
  have hdescent : baseEnd_3203231 < baseStart_3203231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203264 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_3203264 : Nat := 118140960795 + 3203264 * 2 ^ 59
def prefixEnd_3203264 : Nat := 4983230072969 + 3 ^ 40 * 3203264 * 2
def baseEnd_3203264 : Nat := 1644814095243860448568463

theorem tailTrace_3203264 : CollatzResearch.WordTrace tailWord_3203264 prefixEnd_3203264 1644814095243860448568463 := by
  unfold tailWord_3203264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58416318133564538390764423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77888424178086051187685897 58416318133564538390764423)
  ·
    refine ⟨87624477200346807586146635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58416318133564538390764423 87624477200346807586146635)
    ·
      refine ⟨131436715800520211379219953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87624477200346807586146635 131436715800520211379219953)
      ·
        refine ⟨98577536850390158534414965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131436715800520211379219953 98577536850390158534414965)
        ·
          refine ⟨9241644079724077362601403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98577536850390158534414965 9241644079724077362601403)
          ·
            refine ⟨13862466119586116043902105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241644079724077362601403 13862466119586116043902105)
            ·
              refine ⟨10396849589689587032926579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862466119586116043902105 10396849589689587032926579)
              ·
                refine ⟨15595274384534380549389869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10396849589689587032926579 15595274384534380549389869)
                ·
                  refine ⟨5848227894200392706021201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15595274384534380549389869 5848227894200392706021201)
                  ·
                    refine ⟨4386170920650294529515901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5848227894200392706021201 4386170920650294529515901)
                    ·
                      refine ⟨1644814095243860448568463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386170920650294529515901 1644814095243860448568463)
                      ·
                        rfl

theorem cell23_3203264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_3203264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203264 prefixEnd_3203264 := by exact prefixLift 3203264
  have htrace : WordTrace (prefixWord ++ tailWord_3203264) baseStart_3203264 baseEnd_3203264 := by
    simpa [prefixWord, tailWord_3203264, baseEnd_3203264] using wordTrace_append hprefix tailTrace_3203264
  have hstable : (prefixWord ++ tailWord_3203264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203264).length < 2 ^ (prefixWord ++ tailWord_3203264).sum := by decide
  have hdescent : baseEnd_3203264 < baseStart_3203264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203265 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3203265 : Nat := 118140960795 + 3203265 * 2 ^ 59
def prefixEnd_3203265 : Nat := 4983230072969 + 3 ^ 40 * 3203265 * 2
def baseEnd_3203265 : Nat := 1644814608724514944655959

theorem tailTrace_3203265 : CollatzResearch.WordTrace tailWord_3203265 prefixEnd_3203265 1644814608724514944655959 := by
  unfold tailWord_3203265
  simp only [CollatzResearch.WordTrace]
  refine ⟨116832672740125453952315249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77888448493416969301543499 116832672740125453952315249)
  ·
    refine ⟨87624504555094090464236437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116832672740125453952315249 87624504555094090464236437)
    ·
      refine ⟨4107398651020035490511083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87624504555094090464236437 4107398651020035490511083)
      ·
        refine ⟨6161097976530053235766625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107398651020035490511083 6161097976530053235766625)
        ·
          refine ⟨4620823482397539926824969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161097976530053235766625 4620823482397539926824969)
          ·
            refine ⟨3465617611798154945118727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4620823482397539926824969 3465617611798154945118727)
            ·
              refine ⟨5198426417697232417678091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465617611798154945118727 5198426417697232417678091)
              ·
                refine ⟨7797639626545848626517137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198426417697232417678091 7797639626545848626517137)
                ·
                  refine ⟨5848229719909386469887853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797639626545848626517137 5848229719909386469887853)
                  ·
                    refine ⟨2193086144966019926207945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5848229719909386469887853 2193086144966019926207945)
                    ·
                      refine ⟨1644814608724514944655959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193086144966019926207945 1644814608724514944655959)
                      ·
                        rfl

theorem cell23_3203265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3203265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203265 prefixEnd_3203265 := by exact prefixLift 3203265
  have htrace : WordTrace (prefixWord ++ tailWord_3203265) baseStart_3203265 baseEnd_3203265 := by
    simpa [prefixWord, tailWord_3203265, baseEnd_3203265] using wordTrace_append hprefix tailTrace_3203265
  have hstable : (prefixWord ++ tailWord_3203265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203265).length < 2 ^ (prefixWord ++ tailWord_3203265).sum := by decide
  have hdescent : baseEnd_3203265 < baseStart_3203265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203278 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_3203278 : Nat := 118140960795 + 3203278 * 2 ^ 59
def prefixEnd_3203278 : Nat := 4983230072969 + 3 ^ 40 * 3203278 * 2
def baseEnd_3203278 : Nat := 1644821283973023393793399

theorem tailTrace_3203278 : CollatzResearch.WordTrace tailWord_3203278 prefixEnd_3203278 1644821283973023393793399 := by
  unfold tailWord_3203278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604143361134794646567311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77888764592718904781692325 14604143361134794646567311)
  ·
    refine ⟨21906215041702191969850967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14604143361134794646567311 21906215041702191969850967)
    ·
      refine ⟨32859322562553287954776451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21906215041702191969850967 32859322562553287954776451)
      ·
        refine ⟨49288983843829931932164677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32859322562553287954776451 49288983843829931932164677)
        ·
          refine ⟨9241684470718112237280877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49288983843829931932164677 9241684470718112237280877)
          ·
            refine ⟨3465631676519292088980329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9241684470718112237280877 3465631676519292088980329)
            ·
              refine ⟨2599223757389469066735247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465631676519292088980329 2599223757389469066735247)
              ·
                refine ⟨3898835636084203600102871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599223757389469066735247 3898835636084203600102871)
                ·
                  refine ⟨5848253454126305400154307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898835636084203600102871 5848253454126305400154307)
                  ·
                    refine ⟨8772380181189458100231461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5848253454126305400154307 8772380181189458100231461)
                    ·
                      refine ⟨1644821283973023393793399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8772380181189458100231461 1644821283973023393793399)
                      ·
                        rfl

theorem cell23_3203278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_3203278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203278 prefixEnd_3203278 := by exact prefixLift 3203278
  have htrace : WordTrace (prefixWord ++ tailWord_3203278) baseStart_3203278 baseEnd_3203278 := by
    simpa [prefixWord, tailWord_3203278, baseEnd_3203278] using wordTrace_append hprefix tailTrace_3203278
  have hstable : (prefixWord ++ tailWord_3203278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203278).length < 2 ^ (prefixWord ++ tailWord_3203278).sum := by decide
  have hdescent : baseEnd_3203278 < baseStart_3203278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203281 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_3203281 : Nat := 118140960795 + 3203281 * 2 ^ 59
def prefixEnd_3203281 : Nat := 4983230072969 + 3 ^ 40 * 3203281 * 2
def baseEnd_3203281 : Nat := 1644822824414986882055885

theorem tailTrace_3203281 : CollatzResearch.WordTrace tailWord_3203281 prefixEnd_3203281 1644822824414986882055885 := by
  unfold tailWord_3203281
  simp only [CollatzResearch.WordTrace]
  refine ⟨116833256308067488684897697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77888837538711659123265131 116833256308067488684897697)
  ·
    refine ⟨87624942231050616513673273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116833256308067488684897697 87624942231050616513673273)
    ·
      refine ⟨65718706673287962385254955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87624942231050616513673273 65718706673287962385254955)
      ·
        refine ⟨98578060009931943577882433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65718706673287962385254955 98578060009931943577882433)
        ·
          refine ⟨73933545007448957683411825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98578060009931943577882433 73933545007448957683411825)
          ·
            refine ⟨55450158755586718262558869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73933545007448957683411825 55450158755586718262558869)
            ·
              refine ⟨2599226191668127418557447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55450158755586718262558869 2599226191668127418557447)
              ·
                refine ⟨3898839287502191127836171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599226191668127418557447 3898839287502191127836171)
                ·
                  refine ⟨5848258931253286691754257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898839287502191127836171 5848258931253286691754257)
                  ·
                    refine ⟨4386194198439965018815693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5848258931253286691754257 4386194198439965018815693)
                    ·
                      refine ⟨1644822824414986882055885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386194198439965018815693 1644822824414986882055885)
                      ·
                        rfl

theorem cell23_3203281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_3203281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203281 prefixEnd_3203281 := by exact prefixLift 3203281
  have htrace : WordTrace (prefixWord ++ tailWord_3203281) baseStart_3203281 baseEnd_3203281 := by
    simpa [prefixWord, tailWord_3203281, baseEnd_3203281] using wordTrace_append hprefix tailTrace_3203281
  have hstable : (prefixWord ++ tailWord_3203281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203281).length < 2 ^ (prefixWord ++ tailWord_3203281).sum := by decide
  have hdescent : baseEnd_3203281 < baseStart_3203281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203311 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_3203311 : Nat := 118140960795 + 3203311 * 2 ^ 59
def prefixEnd_3203311 : Nat := 4983230072969 + 3 ^ 40 * 3203311 * 2
def baseEnd_3203311 : Nat := 1644838228834621764680747

theorem tailTrace_3203311 : CollatzResearch.WordTrace tailWord_3203311 prefixEnd_3203311 1644838228834621764680747 := by
  unfold tailWord_3203311
  simp only [CollatzResearch.WordTrace]
  refine ⟨116834350497958803808489787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77889566998639202538993191 116834350497958803808489787)
  ·
    refine ⟨175251525746938205712734681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116834350497958803808489787 175251525746938205712734681)
    ·
      refine ⟨131438644310203654284551011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175251525746938205712734681 131438644310203654284551011)
      ·
        refine ⟨197157966465305481426826517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131438644310203654284551011 197157966465305481426826517)
        ·
          refine ⟨9241779678061194441882493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197157966465305481426826517 9241779678061194441882493)
          ·
            refine ⟨3465667379272947915705935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9241779678061194441882493 3465667379272947915705935)
            ·
              refine ⟨5198501068909421873558903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465667379272947915705935 5198501068909421873558903)
              ·
                refine ⟨7797751603364132810338355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198501068909421873558903 7797751603364132810338355)
                ·
                  refine ⟨11696627405046199215507533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7797751603364132810338355 11696627405046199215507533)
                  ·
                    refine ⟨4386235276892324705815325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11696627405046199215507533 4386235276892324705815325)
                    ·
                      refine ⟨1644838228834621764680747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386235276892324705815325 1644838228834621764680747)
                      ·
                        rfl

theorem cell23_3203311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_3203311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203311 prefixEnd_3203311 := by exact prefixLift 3203311
  have htrace : WordTrace (prefixWord ++ tailWord_3203311) baseStart_3203311 baseEnd_3203311 := by
    simpa [prefixWord, tailWord_3203311, baseEnd_3203311] using wordTrace_append hprefix tailTrace_3203311
  have hstable : (prefixWord ++ tailWord_3203311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203311).length < 2 ^ (prefixWord ++ tailWord_3203311).sum := by decide
  have hdescent : baseEnd_3203311 < baseStart_3203311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203337 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_3203337 : Nat := 118140960795 + 3203337 * 2 ^ 59
def prefixEnd_3203337 : Nat := 4983230072969 + 3 ^ 40 * 3203337 * 2
def baseEnd_3203337 : Nat := 1644851579331638662955627

theorem tailTrace_3203337 : CollatzResearch.WordTrace tailWord_3203337 prefixEnd_3203337 1644851579331638662955627 := by
  unfold tailWord_3203337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116835298795864610248936265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77890199197243073499290843 116835298795864610248936265)
  ·
    refine ⟨87626474096898457686702199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116835298795864610248936265 87626474096898457686702199)
    ·
      refine ⟨131439711145347686530053299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87626474096898457686702199 131439711145347686530053299)
      ·
        refine ⟨197159566718021529795079949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131439711145347686530053299 197159566718021529795079949)
        ·
          refine ⟨73934837519258073673154981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197159566718021529795079949 73934837519258073673154981)
          ·
            refine ⟨13862782034860888813716559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73934837519258073673154981 13862782034860888813716559)
            ·
              refine ⟨20794173052291333220574839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13862782034860888813716559 20794173052291333220574839)
              ·
                refine ⟨31191259578436999830862259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20794173052291333220574839 31191259578436999830862259)
                ·
                  refine ⟨46786889367655499746293389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31191259578436999830862259 46786889367655499746293389)
                  ·
                    refine ⟨17545083512870812404860021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46786889367655499746293389 17545083512870812404860021)
                    ·
                      refine ⟨1644851579331638662955627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17545083512870812404860021 1644851579331638662955627)
                      ·
                        rfl

theorem cell23_3203337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_3203337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203337 prefixEnd_3203337 := by exact prefixLift 3203337
  have htrace : WordTrace (prefixWord ++ tailWord_3203337) baseStart_3203337 baseEnd_3203337 := by
    simpa [prefixWord, tailWord_3203337, baseEnd_3203337] using wordTrace_append hprefix tailTrace_3203337
  have hstable : (prefixWord ++ tailWord_3203337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203337).length < 2 ^ (prefixWord ++ tailWord_3203337).sum := by decide
  have hdescent : baseEnd_3203337 < baseStart_3203337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203347 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_3203347 : Nat := 118140960795 + 3203347 * 2 ^ 59
def prefixEnd_3203347 : Nat := 4983230072969 + 3 ^ 40 * 3203347 * 2
def baseEnd_3203347 : Nat := 1644856714138183623830581

theorem tailTrace_3203347 : CollatzResearch.WordTrace tailWord_3203347 prefixEnd_3203347 1644856714138183623830581 := by
  unfold tailWord_3203347
  simp only [CollatzResearch.WordTrace]
  refine ⟨116835663525828381956800295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77890442350552254637866863 116835663525828381956800295)
  ·
    refine ⟨175253495288742572935200443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116835663525828381956800295 175253495288742572935200443)
    ·
      refine ⟨262880242933113859402800665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175253495288742572935200443 262880242933113859402800665)
      ·
        refine ⟨197160182199835394552100499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262880242933113859402800665 197160182199835394552100499)
        ·
          refine ⟨295740273299753091828150749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197160182199835394552100499 295740273299753091828150749)
          ·
            refine ⟨110902602487407409435556531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295740273299753091828150749 110902602487407409435556531)
            ·
              refine ⟨166353903731111114153334797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110902602487407409435556531 166353903731111114153334797)
              ·
                refine ⟨62382713899166667807500549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166353903731111114153334797 62382713899166667807500549)
                ·
                  refine ⟨11696758856093750213906353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62382713899166667807500549 11696758856093750213906353)
                  ·
                    refine ⟨8772569142070312660429765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11696758856093750213906353 8772569142070312660429765)
                    ·
                      refine ⟨1644856714138183623830581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8772569142070312660429765 1644856714138183623830581)
                      ·
                        rfl

theorem cell23_3203347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_3203347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203347 prefixEnd_3203347 := by exact prefixLift 3203347
  have htrace : WordTrace (prefixWord ++ tailWord_3203347) baseStart_3203347 baseEnd_3203347 := by
    simpa [prefixWord, tailWord_3203347, baseEnd_3203347] using wordTrace_append hprefix tailTrace_3203347
  have hstable : (prefixWord ++ tailWord_3203347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203347).length < 2 ^ (prefixWord ++ tailWord_3203347).sum := by decide
  have hdescent : baseEnd_3203347 < baseStart_3203347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203404 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_3203404 : Nat := 118140960795 + 3203404 * 2 ^ 59
def prefixEnd_3203404 : Nat := 4983230072969 + 3 ^ 40 * 3203404 * 2
def baseEnd_3203404 : Nat := 548295327511829966939273

theorem tailTrace_3203404 : CollatzResearch.WordTrace tailWord_3203404 prefixEnd_3203404 548295327511829966939273 := by
  unfold tailWord_3203404
  simp only [CollatzResearch.WordTrace]
  refine ⟨58418871243310940345812633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77891828324414587127750177 58418871243310940345812633)
  ·
    refine ⟨43814153432483205259359475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58418871243310940345812633 43814153432483205259359475)
    ·
      refine ⟨65721230148724807889039213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43814153432483205259359475 65721230148724807889039213)
      ·
        refine ⟨24645461305771802958389705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65721230148724807889039213 24645461305771802958389705)
        ·
          refine ⟨18484095979328852218792279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24645461305771802958389705 18484095979328852218792279)
          ·
            refine ⟨27726143968993278328188419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18484095979328852218792279 27726143968993278328188419)
            ·
              refine ⟨41589215953489917492282629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27726143968993278328188419 41589215953489917492282629)
              ·
                refine ⟨7797977991279359529802993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41589215953489917492282629 7797977991279359529802993)
                ·
                  refine ⟨5848483493459519647352245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797977991279359529802993 5848483493459519647352245)
                  ·
                    refine ⟨548295327511829966939273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5848483493459519647352245 548295327511829966939273)
                    ·
                      rfl

theorem cell23_3203404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_3203404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203404 prefixEnd_3203404 := by exact prefixLift 3203404
  have htrace : WordTrace (prefixWord ++ tailWord_3203404) baseStart_3203404 baseEnd_3203404 := by
    simpa [prefixWord, tailWord_3203404, baseEnd_3203404] using wordTrace_append hprefix tailTrace_3203404
  have hstable : (prefixWord ++ tailWord_3203404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203404).length < 2 ^ (prefixWord ++ tailWord_3203404).sum := by decide
  have hdescent : baseEnd_3203404 < baseStart_3203404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203408 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 5]
def baseStart_3203408 : Nat := 118140960795 + 3203408 * 2 ^ 59
def prefixEnd_3203408 : Nat := 4983230072969 + 3 ^ 40 * 3203408 * 2
def baseEnd_3203408 : Nat := 182765337384234209463089

theorem tailTrace_3203408 : CollatzResearch.WordTrace tailWord_3203408 prefixEnd_3203408 182765337384234209463089 := by
  unfold tailWord_3203408
  simp only [CollatzResearch.WordTrace]
  refine ⟨58418944189303694687385439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77891925585738259583180585 58418944189303694687385439)
  ·
    refine ⟨87628416283955542031078159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58418944189303694687385439 87628416283955542031078159)
    ·
      refine ⟨131442624425933313046617239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87628416283955542031078159 131442624425933313046617239)
      ·
        refine ⟨197163936638899969569925859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131442624425933313046617239 197163936638899969569925859)
        ·
          refine ⟨295745904958349954354888789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197163936638899969569925859 295745904958349954354888789)
          ·
            refine ⟨3465772323730663527596353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 295745904958349954354888789 3465772323730663527596353)
            ·
              refine ⟨2599329242797997645697265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465772323730663527596353 2599329242797997645697265)
              ·
                refine ⟨1949496932098498234272949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599329242797997645697265 1949496932098498234272949)
                ·
                  refine ⟨182765337384234209463089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1949496932098498234272949 182765337384234209463089)
                  ·
                    rfl

theorem cell23_3203408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 5].length) (baseStart_3203408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203408 prefixEnd_3203408 := by exact prefixLift 3203408
  have htrace : WordTrace (prefixWord ++ tailWord_3203408) baseStart_3203408 baseEnd_3203408 := by
    simpa [prefixWord, tailWord_3203408, baseEnd_3203408] using wordTrace_append hprefix tailTrace_3203408
  have hstable : (prefixWord ++ tailWord_3203408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203408).length < 2 ^ (prefixWord ++ tailWord_3203408).sum := by decide
  have hdescent : baseEnd_3203408 < baseStart_3203408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203417 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_3203417 : Nat := 118140960795 + 3203417 * 2 ^ 59
def prefixEnd_3203417 : Nat := 4983230072969 + 3 ^ 40 * 3203417 * 2
def baseEnd_3203417 : Nat := 548297552594666116651753

theorem tailTrace_3203417 : CollatzResearch.WordTrace tailWord_3203417 prefixEnd_3203417 548297552594666116651753 := by
  unfold tailWord_3203417
  simp only [CollatzResearch.WordTrace]
  refine ⟨116838216635574783911848505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77892144423716522607899003 116838216635574783911848505)
  ·
    refine ⟨87628662476681087933886379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116838216635574783911848505 87628662476681087933886379)
    ·
      refine ⟨131442993715021631900829569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87628662476681087933886379 131442993715021631900829569)
      ·
        refine ⟨98582245286266223925622177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131442993715021631900829569 98582245286266223925622177)
        ·
          refine ⟨73936683964699667944216633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98582245286266223925622177 73936683964699667944216633)
          ·
            refine ⟨55452512973524750958162475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73936683964699667944216633 55452512973524750958162475)
            ·
              refine ⟨83178769460287126437243713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55452512973524750958162475 83178769460287126437243713)
              ·
                refine ⟨62384077095215344827932785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83178769460287126437243713 62384077095215344827932785)
                ·
                  refine ⟨46788057821411508620949589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62384077095215344827932785 46788057821411508620949589)
                  ·
                    refine ⟨548297552594666116651753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46788057821411508620949589 548297552594666116651753)
                    ·
                      rfl

theorem cell23_3203417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_3203417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203417 prefixEnd_3203417 := by exact prefixLift 3203417
  have htrace : WordTrace (prefixWord ++ tailWord_3203417) baseStart_3203417 baseEnd_3203417 := by
    simpa [prefixWord, tailWord_3203417, baseEnd_3203417] using wordTrace_append hprefix tailTrace_3203417
  have hstable : (prefixWord ++ tailWord_3203417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203417).length < 2 ^ (prefixWord ++ tailWord_3203417).sum := by decide
  have hdescent : baseEnd_3203417 < baseStart_3203417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203464 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 8]
def baseStart_3203464 : Nat := 118140960795 + 3203464 * 2 ^ 59
def prefixEnd_3203464 : Nat := 4983230072969 + 3 ^ 40 * 3203464 * 2
def baseEnd_3203464 : Nat := 182768532374973296229727

theorem tailTrace_3203464 : CollatzResearch.WordTrace tailWord_3203464 prefixEnd_3203464 182768532374973296229727 := by
  unfold tailWord_3203464
  simp only [CollatzResearch.WordTrace]
  refine ⟨58419965433202255469404723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77893287244269673959206297 58419965433202255469404723)
  ·
    refine ⟨87629948149803383204107085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58419965433202255469404723 87629948149803383204107085)
    ·
      refine ⟨32861230556176268701540157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87629948149803383204107085 32861230556176268701540157)
      ·
        refine ⟨12322961458566100763077559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32861230556176268701540157 12322961458566100763077559)
        ·
          refine ⟨18484442187849151144616339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322961458566100763077559 18484442187849151144616339)
          ·
            refine ⟨27726663281773726716924509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18484442187849151144616339 27726663281773726716924509)
            ·
              refine ⟨10397498730665147518846691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27726663281773726716924509 10397498730665147518846691)
              ·
                refine ⟨15596248095997721278270037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397498730665147518846691 15596248095997721278270037)
                ·
                  refine ⟨182768532374973296229727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15596248095997721278270037 182768532374973296229727)
                  ·
                    rfl

theorem cell23_3203464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_3203464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203464 prefixEnd_3203464 := by exact prefixLift 3203464
  have htrace : WordTrace (prefixWord ++ tailWord_3203464) baseStart_3203464 baseEnd_3203464 := by
    simpa [prefixWord, tailWord_3203464, baseEnd_3203464] using wordTrace_append hprefix tailTrace_3203464
  have hstable : (prefixWord ++ tailWord_3203464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203464).length < 2 ^ (prefixWord ++ tailWord_3203464).sum := by decide
  have hdescent : baseEnd_3203464 < baseStart_3203464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203468 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_3203468 : Nat := 118140960795 + 3203468 * 2 ^ 59
def prefixEnd_3203468 : Nat := 4983230072969 + 3 ^ 40 * 3203468 * 2
def baseEnd_3203468 : Nat := 548306281765792550139175

theorem tailTrace_3203468 : CollatzResearch.WordTrace tailWord_3203468 prefixEnd_3203468 548306281765792550139175 := by
  unfold tailWord_3203468
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420038379195009810977529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77893384505593346414636705 58420038379195009810977529)
  ·
    refine ⟨43815028784396257358233147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58420038379195009810977529 43815028784396257358233147)
    ·
      refine ⟨65722543176594386037349721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43815028784396257358233147 65722543176594386037349721)
      ·
        refine ⟨49291907382445789528012291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65722543176594386037349721 49291907382445789528012291)
        ·
          refine ⟨73937861073668684292018437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49291907382445789528012291 73937861073668684292018437)
          ·
            refine ⟨13863348951312878304753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73937861073668684292018437 13863348951312878304753457)
            ·
              refine ⟨10397511713484658728565093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13863348951312878304753457 10397511713484658728565093)
              ·
                refine ⟨1949533446278373511605955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10397511713484658728565093 1949533446278373511605955)
                ·
                  refine ⟨2924300169417560267408933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949533446278373511605955 2924300169417560267408933)
                  ·
                    refine ⟨548306281765792550139175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2924300169417560267408933 548306281765792550139175)
                    ·
                      rfl

theorem cell23_3203468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_3203468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203468 prefixEnd_3203468 := by exact prefixLift 3203468
  have htrace : WordTrace (prefixWord ++ tailWord_3203468) baseStart_3203468 baseEnd_3203468 := by
    simpa [prefixWord, tailWord_3203468, baseEnd_3203468] using wordTrace_append hprefix tailTrace_3203468
  have hstable : (prefixWord ++ tailWord_3203468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203468).length < 2 ^ (prefixWord ++ tailWord_3203468).sum := by decide
  have hdescent : baseEnd_3203468 < baseStart_3203468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203481 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 6]
def baseStart_3203481 : Nat := 118140960795 + 3203481 * 2 ^ 59
def prefixEnd_3203481 : Nat := 4983230072969 + 3 ^ 40 * 3203481 * 2
def baseEnd_3203481 : Nat := 182769502282876233283885

theorem tailTrace_3203481 : CollatzResearch.WordTrace tailWord_3203481 prefixEnd_3203481 182769502282876233283885 := by
  unfold tailWord_3203481
  simp only [CollatzResearch.WordTrace]
  refine ⟨116840550907342922842178297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77893700604895281894785531 116840550907342922842178297)
  ·
    refine ⟨87630413180507192131633723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116840550907342922842178297 87630413180507192131633723)
    ·
      refine ⟨131445619770760788197450585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87630413180507192131633723 131445619770760788197450585)
      ·
        refine ⟨98584214828070591148087939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131445619770760788197450585 98584214828070591148087939)
        ·
          refine ⟨147876322242105886722131909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98584214828070591148087939 147876322242105886722131909)
          ·
            refine ⟨27726810420394853760399733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147876322242105886722131909 27726810420394853760399733)
            ·
              refine ⟨2599388476912017540037475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27726810420394853760399733 2599388476912017540037475)
              ·
                refine ⟨3899082715368026310056213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599388476912017540037475 3899082715368026310056213)
                ·
                  refine ⟨182769502282876233283885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3899082715368026310056213 182769502282876233283885)
                  ·
                    rfl

theorem cell23_3203481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 6].length) (baseStart_3203481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203481 prefixEnd_3203481 := by exact prefixLift 3203481
  have htrace : WordTrace (prefixWord ++ tailWord_3203481) baseStart_3203481 baseEnd_3203481 := by
    simpa [prefixWord, tailWord_3203481, baseEnd_3203481] using wordTrace_append hprefix tailTrace_3203481
  have hstable : (prefixWord ++ tailWord_3203481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203481).length < 2 ^ (prefixWord ++ tailWord_3203481).sum := by decide
  have hdescent : baseEnd_3203481 < baseStart_3203481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203511 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 1, 5]
def baseStart_3203511 : Nat := 118140960795 + 3203511 * 2 ^ 59
def prefixEnd_3203511 : Nat := 4983230072969 + 3 ^ 40 * 3203511 * 2
def baseEnd_3203511 : Nat := 548313641655173660726609

theorem tailTrace_3203511 : CollatzResearch.WordTrace tailWord_3203511 prefixEnd_3203511 548313641655173660726609 := by
  unfold tailWord_3203511
  simp only [CollatzResearch.WordTrace]
  refine ⟨116841645097234237965770387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77894430064822825310513591 116841645097234237965770387)
  ·
    refine ⟨175262467645851356948655581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116841645097234237965770387 175262467645851356948655581)
    ·
      refine ⟨65723425367194258855745843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175262467645851356948655581 65723425367194258855745843)
      ·
        refine ⟨98585138050791388283618765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65723425367194258855745843 98585138050791388283618765)
        ·
          refine ⟨36969426769046770606357037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98585138050791388283618765 36969426769046770606357037)
          ·
            refine ⟨13863535038392538977383889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36969426769046770606357037 13863535038392538977383889)
            ·
              refine ⟨10397651278794404233037917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13863535038392538977383889 10397651278794404233037917)
              ·
                refine ⟨3899119229547901587389219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10397651278794404233037917 3899119229547901587389219)
                ·
                  refine ⟨5848678844321852381083829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899119229547901587389219 5848678844321852381083829)
                  ·
                    refine ⟨548313641655173660726609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5848678844321852381083829 548313641655173660726609)
                    ·
                      rfl

theorem cell23_3203511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_3203511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203511 prefixEnd_3203511 := by exact prefixLift 3203511
  have htrace : WordTrace (prefixWord ++ tailWord_3203511) baseStart_3203511 baseEnd_3203511 := by
    simpa [prefixWord, tailWord_3203511, baseEnd_3203511] using wordTrace_append hprefix tailTrace_3203511
  have hstable : (prefixWord ++ tailWord_3203511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203511).length < 2 ^ (prefixWord ++ tailWord_3203511).sum := by decide
  have hdescent : baseEnd_3203511 < baseStart_3203511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203518 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_3203518 : Nat := 118140960795 + 3203518 * 2 ^ 59
def prefixEnd_3203518 : Nat := 4983230072969 + 3 ^ 40 * 3203518 * 2
def baseEnd_3203518 : Nat := 1644944519330102454792295

theorem tailTrace_3203518 : CollatzResearch.WordTrace tailWord_3203518 prefixEnd_3203518 1644944519330102454792295 := by
  unfold tailWord_3203518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605237551026109770159401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77894600272139252107516805 14605237551026109770159401)
  ·
    refine ⟨10953928163269582327619551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14605237551026109770159401 10953928163269582327619551)
    ·
      refine ⟨16430892244904373491429327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10953928163269582327619551 16430892244904373491429327)
      ·
        refine ⟨24646338367356560237143991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16430892244904373491429327 24646338367356560237143991)
        ·
          refine ⟨36969507551034840355715987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24646338367356560237143991 36969507551034840355715987)
          ·
            refine ⟨55454261326552260533573981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36969507551034840355715987 55454261326552260533573981)
            ·
              refine ⟨20795347997457097700090243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55454261326552260533573981 20795347997457097700090243)
              ·
                refine ⟨31193021996185646550135365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20795347997457097700090243 31193021996185646550135365)
                ·
                  refine ⟨5848691624284808728150381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31193021996185646550135365 5848691624284808728150381)
                  ·
                    refine ⟨2193259359106803273056393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5848691624284808728150381 2193259359106803273056393)
                    ·
                      refine ⟨1644944519330102454792295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193259359106803273056393 1644944519330102454792295)
                      ·
                        rfl

theorem cell23_3203518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_3203518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203518 prefixEnd_3203518 := by exact prefixLift 3203518
  have htrace : WordTrace (prefixWord ++ tailWord_3203518) baseStart_3203518 baseEnd_3203518 := by
    simpa [prefixWord, tailWord_3203518, baseEnd_3203518] using wordTrace_append hprefix tailTrace_3203518
  have hstable : (prefixWord ++ tailWord_3203518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203518).length < 2 ^ (prefixWord ++ tailWord_3203518).sum := by decide
  have hdescent : baseEnd_3203518 < baseStart_3203518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203581 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_3203581 : Nat := 118140960795 + 3203581 * 2 ^ 59
def prefixEnd_3203581 : Nat := 4983230072969 + 3 ^ 40 * 3203581 * 2
def baseEnd_3203581 : Nat := 1644976868611335708304505

theorem tailTrace_3203581 : CollatzResearch.WordTrace tailWord_3203581 prefixEnd_3203581 1644976868611335708304505 := by
  unfold tailWord_3203581
  simp only [CollatzResearch.WordTrace]
  refine ⟨116844198206980639920818597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77896132137987093280545731 116844198206980639920818597)
  ·
    refine ⟨21908287163808869985153487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116844198206980639920818597 21908287163808869985153487)
    ·
      refine ⟨32862430745713304977730231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908287163808869985153487 32862430745713304977730231)
      ·
        refine ⟨49293646118569957466595347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32862430745713304977730231 49293646118569957466595347)
        ·
          refine ⟨73940469177854936199893021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49293646118569957466595347 73940469177854936199893021)
          ·
            refine ⟨27727675941695601074959883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73940469177854936199893021 27727675941695601074959883)
            ·
              refine ⟨41591513912543401612439825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27727675941695601074959883 41591513912543401612439825)
              ·
                refine ⟨31193635434407551209329869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41591513912543401612439825 31193635434407551209329869)
                ·
                  refine ⟨11697613287902831703498701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31193635434407551209329869 11697613287902831703498701)
                  ·
                    refine ⟨4386604982963561888812013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11697613287902831703498701 4386604982963561888812013)
                    ·
                      refine ⟨1644976868611335708304505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386604982963561888812013 1644976868611335708304505)
                      ·
                        rfl

theorem cell23_3203581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_3203581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203581 prefixEnd_3203581 := by exact prefixLift 3203581
  have htrace : WordTrace (prefixWord ++ tailWord_3203581) baseStart_3203581 baseEnd_3203581 := by
    simpa [prefixWord, tailWord_3203581, baseEnd_3203581] using wordTrace_append hprefix tailTrace_3203581
  have hstable : (prefixWord ++ tailWord_3203581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203581).length < 2 ^ (prefixWord ++ tailWord_3203581).sum := by decide
  have hdescent : baseEnd_3203581 < baseStart_3203581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203588 : List Nat := [2, 3, 2, 3, 1, 3, 1, 8]
def baseStart_3203588 : Nat := 118140960795 + 3203588 * 2 ^ 59
def prefixEnd_3203588 : Nat := 4983230072969 + 3 ^ 40 * 3203588 * 2
def baseEnd_3203588 : Nat := 60925202332441377070999

theorem tailTrace_3203588 : CollatzResearch.WordTrace tailWord_3203588 prefixEnd_3203588 60925202332441377070999 := by
  unfold tailWord_3203588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58422226758977640058161709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77896302345303520077548945 58422226758977640058161709)
  ·
    refine ⟨21908335034616615021810641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58422226758977640058161709 21908335034616615021810641)
    ·
      refine ⟨16431251275962461266357981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21908335034616615021810641 16431251275962461266357981)
      ·
        refine ⟨6161719228485922974884243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16431251275962461266357981 6161719228485922974884243)
        ·
          refine ⟨9242578842728884462326365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161719228485922974884243 9242578842728884462326365)
          ·
            refine ⟨3465967066023331673372387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9242578842728884462326365 3465967066023331673372387)
            ·
              refine ⟨5198950599034997510058581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465967066023331673372387 5198950599034997510058581)
              ·
                refine ⟨60925202332441377070999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5198950599034997510058581 60925202332441377070999)
                ·
                  rfl

theorem cell23_3203588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 8].length) (baseStart_3203588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203588 prefixEnd_3203588 := by exact prefixLift 3203588
  have htrace : WordTrace (prefixWord ++ tailWord_3203588) baseStart_3203588 baseEnd_3203588 := by
    simpa [prefixWord, tailWord_3203588, baseEnd_3203588] using wordTrace_append hprefix tailTrace_3203588
  have hstable : (prefixWord ++ tailWord_3203588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203588).length < 2 ^ (prefixWord ++ tailWord_3203588).sum := by decide
  have hdescent : baseEnd_3203588 < baseStart_3203588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203598 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3203598 : Nat := 118140960795 + 3203598 * 2 ^ 59
def prefixEnd_3203598 : Nat := 4983230072969 + 3 ^ 40 * 3203598 * 2
def baseEnd_3203598 : Nat := 1644985597782462141791927

theorem tailTrace_3203598 : CollatzResearch.WordTrace tailWord_3203598 prefixEnd_3203598 1644985597782462141791927 := by
  unfold tailWord_3203598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605602280989881478023431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77896545498612701216124965 14605602280989881478023431)
  ·
    refine ⟨21908403421484822217035147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14605602280989881478023431 21908403421484822217035147)
    ·
      refine ⟨32862605132227233325552721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908403421484822217035147 32862605132227233325552721)
      ·
        refine ⟨24646953849170424994164541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32862605132227233325552721 24646953849170424994164541)
        ·
          refine ⟨9242607693438909372811703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24646953849170424994164541 9242607693438909372811703)
          ·
            refine ⟨13863911540158364059217555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242607693438909372811703 13863911540158364059217555)
            ·
              refine ⟨20795867310237546088826333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13863911540158364059217555 20795867310237546088826333)
              ·
                refine ⟨7798450241339079783309875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20795867310237546088826333 7798450241339079783309875)
                ·
                  refine ⟨11697675362008619674964813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798450241339079783309875 11697675362008619674964813)
                  ·
                    refine ⟨4386628260753232378111805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11697675362008619674964813 4386628260753232378111805)
                    ·
                      refine ⟨1644985597782462141791927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386628260753232378111805 1644985597782462141791927)
                      ·
                        rfl

theorem cell23_3203598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3203598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203598 prefixEnd_3203598 := by exact prefixLift 3203598
  have htrace : WordTrace (prefixWord ++ tailWord_3203598) baseStart_3203598 baseEnd_3203598 := by
    simpa [prefixWord, tailWord_3203598, baseEnd_3203598] using wordTrace_append hprefix tailTrace_3203598
  have hstable : (prefixWord ++ tailWord_3203598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203598).length < 2 ^ (prefixWord ++ tailWord_3203598).sum := by decide
  have hdescent : baseEnd_3203598 < baseStart_3203598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203655 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 1, 4, 2]
def baseStart_3203655 : Nat := 118140960795 + 3203655 * 2 ^ 59
def prefixEnd_3203655 : Nat := 4983230072969 + 3 ^ 40 * 3203655 * 2
def baseEnd_3203655 : Nat := 1645014866179768418779165

theorem tailTrace_3203655 : CollatzResearch.WordTrace tailWord_3203655 prefixEnd_3203655 1645014866179768418779165 := by
  unfold tailWord_3203655
  simp only [CollatzResearch.WordTrace]
  refine ⟨116846897208712550559012419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77897931472475033706008279 116846897208712550559012419)
  ·
    refine ⟨175270345813068825838518629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116846897208712550559012419 175270345813068825838518629)
    ·
      refine ⟨32863189839950404844722243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175270345813068825838518629 32863189839950404844722243)
      ·
        refine ⟨49294784759925607267083365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32863189839950404844722243 49294784759925607267083365)
        ·
          refine ⟨9242772142486051362578131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49294784759925607267083365 9242772142486051362578131)
          ·
            refine ⟨13864158213729077043867197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242772142486051362578131 13864158213729077043867197)
            ·
              refine ⟨5199059330148403891450199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13864158213729077043867197 5199059330148403891450199)
              ·
                refine ⟨7798588995222605837175299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199059330148403891450199 7798588995222605837175299)
                ·
                  refine ⟨11697883492833908755762949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798588995222605837175299 11697883492833908755762949)
                  ·
                    refine ⟨2193353154906357891705553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11697883492833908755762949 2193353154906357891705553)
                    ·
                      refine ⟨1645014866179768418779165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193353154906357891705553 1645014866179768418779165)
                      ·
                        rfl

theorem cell23_3203655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_3203655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203655 prefixEnd_3203655 := by exact prefixLift 3203655
  have htrace : WordTrace (prefixWord ++ tailWord_3203655) baseStart_3203655 baseEnd_3203655 := by
    simpa [prefixWord, tailWord_3203655, baseEnd_3203655] using wordTrace_append hprefix tailTrace_3203655
  have hstable : (prefixWord ++ tailWord_3203655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203655).length < 2 ^ (prefixWord ++ tailWord_3203655).sum := by decide
  have hdescent : baseEnd_3203655 < baseStart_3203655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203711 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_3203711 : Nat := 118140960795 + 3203711 * 2 ^ 59
def prefixEnd_3203711 : Nat := 4983230072969 + 3 ^ 40 * 3203711 * 2
def baseEnd_3203711 : Nat := 1645043621096420199678907

theorem tailTrace_3203711 : CollatzResearch.WordTrace tailWord_3203711 prefixEnd_3203711 1645043621096420199678907 := by
  unfold tailWord_3203711
  simp only [CollatzResearch.WordTrace]
  refine ⟨116848939696509672123050987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77899293131006448082033991 116848939696509672123050987)
  ·
    refine ⟨175273409544764508184576481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116848939696509672123050987 175273409544764508184576481)
    ·
      refine ⟨131455057158573381138432361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175273409544764508184576481 131455057158573381138432361)
      ·
        refine ⟨98591292868930035853824271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131455057158573381138432361 98591292868930035853824271)
        ·
          refine ⟨147886939303395053780736407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98591292868930035853824271 147886939303395053780736407)
          ·
            refine ⟨221830408955092580671104611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147886939303395053780736407 221830408955092580671104611)
            ·
              refine ⟨332745613432638871006656917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221830408955092580671104611 332745613432638871006656917)
              ·
                refine ⟨15597450629654947078437043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 332745613432638871006656917 15597450629654947078437043)
                ·
                  refine ⟨23396175944482420617655565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15597450629654947078437043 23396175944482420617655565)
                  ·
                    refine ⟨8773565979180907731620837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23396175944482420617655565 8773565979180907731620837)
                    ·
                      refine ⟨1645043621096420199678907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8773565979180907731620837 1645043621096420199678907)
                      ·
                        rfl

theorem cell23_3203711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_3203711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203711 prefixEnd_3203711 := by exact prefixLift 3203711
  have htrace : WordTrace (prefixWord ++ tailWord_3203711) baseStart_3203711 baseEnd_3203711 := by
    simpa [prefixWord, tailWord_3203711, baseEnd_3203711] using wordTrace_append hprefix tailTrace_3203711
  have hstable : (prefixWord ++ tailWord_3203711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203711).length < 2 ^ (prefixWord ++ tailWord_3203711).sum := by decide
  have hdescent : baseEnd_3203711 < baseStart_3203711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203728 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2]
def baseStart_3203728 : Nat := 118140960795 + 3203728 * 2 ^ 59
def prefixEnd_3203728 : Nat := 4983230072969 + 3 ^ 40 * 3203728 * 2
def baseEnd_3203728 : Nat := 1645052350267546633166329

theorem tailTrace_3203728 : CollatzResearch.WordTrace tailWord_3203728 prefixEnd_3203728 1645052350267546633166329 := by
  unfold tailWord_3203728
  simp only [CollatzResearch.WordTrace]
  refine ⟨58424779868724042013209919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77899706491632056017613225 58424779868724042013209919)
  ·
    refine ⟨87637169803086063019814879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58424779868724042013209919 87637169803086063019814879)
    ·
      refine ⟨131455754704629094529722319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87637169803086063019814879 131455754704629094529722319)
      ·
        refine ⟨197183632056943641794583479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131455754704629094529722319 197183632056943641794583479)
        ·
          refine ⟨295775448085415462691875219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197183632056943641794583479 295775448085415462691875219)
          ·
            refine ⟨443663172128123194037812829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295775448085415462691875219 443663172128123194037812829)
            ·
              refine ⟨166373689548046197764179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443663172128123194037812829 166373689548046197764179811)
              ·
                refine ⟨249560534322069296646269717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166373689548046197764179811 249560534322069296646269717)
                ·
                  refine ⟨11698150046346998280293893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249560534322069296646269717 11698150046346998280293893)
                  ·
                    refine ⟨2193403133690062177555105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11698150046346998280293893 2193403133690062177555105)
                    ·
                      refine ⟨1645052350267546633166329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193403133690062177555105 1645052350267546633166329)
                      ·
                        rfl

theorem cell23_3203728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 4, 2].length) (baseStart_3203728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203728 prefixEnd_3203728 := by exact prefixLift 3203728
  have htrace : WordTrace (prefixWord ++ tailWord_3203728) baseStart_3203728 baseEnd_3203728 := by
    simpa [prefixWord, tailWord_3203728, baseEnd_3203728] using wordTrace_append hprefix tailTrace_3203728
  have hstable : (prefixWord ++ tailWord_3203728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203728).length < 2 ^ (prefixWord ++ tailWord_3203728).sum := by decide
  have hdescent : baseEnd_3203728 < baseStart_3203728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203791 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_3203791 : Nat := 118140960795 + 3203791 * 2 ^ 59
def prefixEnd_3203791 : Nat := 4983230072969 + 3 ^ 40 * 3203791 * 2
def baseEnd_3203791 : Nat := 1645084699548779886678539

theorem tailTrace_3203791 : CollatzResearch.WordTrace tailWord_3203791 prefixEnd_3203791 1645084699548779886678539 := by
  unfold tailWord_3203791
  simp only [CollatzResearch.WordTrace]
  refine ⟨116851857536219845785963227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77901238357479897190642151 116851857536219845785963227)
  ·
    refine ⟨175277786304329768678944841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116851857536219845785963227 175277786304329768678944841)
    ·
      refine ⟨131458339728247326509208631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175277786304329768678944841 131458339728247326509208631)
      ·
        refine ⟨197187509592370989763812947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131458339728247326509208631 197187509592370989763812947)
        ·
          refine ⟨295781264388556484645719421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197187509592370989763812947 295781264388556484645719421)
          ·
            refine ⟨110917974145708681742144783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295781264388556484645719421 110917974145708681742144783)
            ·
              refine ⟨166376961218563022613217175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110917974145708681742144783 166376961218563022613217175)
              ·
                refine ⟨249565441827844533919825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166376961218563022613217175 249565441827844533919825763)
                ·
                  refine ⟨374348162741766800879738645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249565441827844533919825763 374348162741766800879738645)
                  ·
                    refine ⟨17547570128520318791237749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 374348162741766800879738645 17547570128520318791237749)
                    ·
                      refine ⟨1645084699548779886678539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17547570128520318791237749 1645084699548779886678539)
                      ·
                        rfl

theorem cell23_3203791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_3203791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203791 prefixEnd_3203791 := by exact prefixLift 3203791
  have htrace : WordTrace (prefixWord ++ tailWord_3203791) baseStart_3203791 baseEnd_3203791 := by
    simpa [prefixWord, tailWord_3203791, baseEnd_3203791] using wordTrace_append hprefix tailTrace_3203791
  have hstable : (prefixWord ++ tailWord_3203791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203791).length < 2 ^ (prefixWord ++ tailWord_3203791).sum := by decide
  have hdescent : baseEnd_3203791 < baseStart_3203791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203812 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_3203812 : Nat := 118140960795 + 3203812 * 2 ^ 59
def prefixEnd_3203812 : Nat := 4983230072969 + 3 ^ 40 * 3203812 * 2
def baseEnd_3203812 : Nat := 1645095482642524304515943

theorem tailTrace_3203812 : CollatzResearch.WordTrace tailWord_3203812 prefixEnd_3203812 1645095482642524304515943 := by
  unfold tailWord_3203812
  simp only [CollatzResearch.WordTrace]
  refine ⟨58426311734571883186238845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77901748979429177581651793 58426311734571883186238845)
  ·
    refine ⟨21909866900464456194839567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58426311734571883186238845 21909866900464456194839567)
    ·
      refine ⟨32864800350696684292259351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21909866900464456194839567 32864800350696684292259351)
      ·
        refine ⟨49297200526045026438389027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32864800350696684292259351 49297200526045026438389027)
        ·
          refine ⟨73945800789067539657583541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49297200526045026438389027 73945800789067539657583541)
          ·
            refine ⟨6932418823975081842898457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73945800789067539657583541 6932418823975081842898457)
            ·
              refine ⟨5199314117981311382173843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932418823975081842898457 5199314117981311382173843)
              ·
                refine ⟨7798971176971967073260765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199314117981311382173843 7798971176971967073260765)
                ·
                  refine ⟨2924614191364487652472787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7798971176971967073260765 2924614191364487652472787)
                  ·
                    refine ⟨4386921287046731478709181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2924614191364487652472787 4386921287046731478709181)
                    ·
                      refine ⟨1645095482642524304515943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386921287046731478709181 1645095482642524304515943)
                      ·
                        rfl

theorem cell23_3203812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_3203812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203812 prefixEnd_3203812 := by exact prefixLift 3203812
  have htrace : WordTrace (prefixWord ++ tailWord_3203812) baseStart_3203812 baseEnd_3203812 := by
    simpa [prefixWord, tailWord_3203812, baseEnd_3203812] using wordTrace_append hprefix tailTrace_3203812
  have hstable : (prefixWord ++ tailWord_3203812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203812).length < 2 ^ (prefixWord ++ tailWord_3203812).sum := by decide
  have hdescent : baseEnd_3203812 < baseStart_3203812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203855 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_3203855 : Nat := 118140960795 + 3203855 * 2 ^ 59
def prefixEnd_3203855 : Nat := 4983230072969 + 3 ^ 40 * 3203855 * 2
def baseEnd_3203855 : Nat := 1645117562310667636278245

theorem tailTrace_3203855 : CollatzResearch.WordTrace tailWord_3203855 prefixEnd_3203855 1645117562310667636278245 := by
  unfold tailWord_3203855
  simp only [CollatzResearch.WordTrace]
  refine ⟨116854191807987984716293019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77902794538658656477528679 116854191807987984716293019)
  ·
    refine ⟨175281287711981977074439529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116854191807987984716293019 175281287711981977074439529)
    ·
      refine ⟨131460965783986482805829647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175281287711981977074439529 131460965783986482805829647)
      ·
        refine ⟨197191448675979724208744471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131460965783986482805829647 197191448675979724208744471)
        ·
          refine ⟨295787173013969586313116707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197191448675979724208744471 295787173013969586313116707)
          ·
            refine ⟨443680759520954379469675061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295787173013969586313116707 443680759520954379469675061)
            ·
              refine ⟨41595071205089473075282037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443680759520954379469675061 41595071205089473075282037)
              ·
                refine ⟨3899537925477138100807691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41595071205089473075282037 3899537925477138100807691)
                ·
                  refine ⟨5849306888215707151211537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899537925477138100807691 5849306888215707151211537)
                  ·
                    refine ⟨4386980166161780363408653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5849306888215707151211537 4386980166161780363408653)
                    ·
                      refine ⟨1645117562310667636278245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4386980166161780363408653 1645117562310667636278245)
                      ·
                        rfl

theorem cell23_3203855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_3203855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203855 prefixEnd_3203855 := by exact prefixLift 3203855
  have htrace : WordTrace (prefixWord ++ tailWord_3203855) baseStart_3203855 baseEnd_3203855 := by
    simpa [prefixWord, tailWord_3203855, baseEnd_3203855] using wordTrace_append hprefix tailTrace_3203855
  have hstable : (prefixWord ++ tailWord_3203855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203855).length < 2 ^ (prefixWord ++ tailWord_3203855).sum := by decide
  have hdescent : baseEnd_3203855 < baseStart_3203855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203918 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3203918 : Nat := 118140960795 + 3203918 * 2 ^ 59
def prefixEnd_3203918 : Nat := 4983230072969 + 3 ^ 40 * 3203918 * 2
def baseEnd_3203918 : Nat := 548383303863966963263485

theorem tailTrace_3203918 : CollatzResearch.WordTrace tailWord_3203918 prefixEnd_3203918 548383303863966963263485 := by
  unfold tailWord_3203918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607061200844968309479551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77904326404506497650557605 14607061200844968309479551)
  ·
    refine ⟨21910591801267452464219327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14607061200844968309479551 21910591801267452464219327)
    ·
      refine ⟨32865887701901178696328991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21910591801267452464219327 32865887701901178696328991)
      ·
        refine ⟨49298831552851768044493487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32865887701901178696328991 49298831552851768044493487)
        ·
          refine ⟨73948247329277652066740231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49298831552851768044493487 73948247329277652066740231)
          ·
            refine ⟨110922370993916478100110347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73948247329277652066740231 110922370993916478100110347)
            ·
              refine ⟨166383556490874717150165521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110922370993916478100110347 166383556490874717150165521)
              ·
                refine ⟨124787667368156037862624141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166383556490874717150165521 124787667368156037862624141)
                ·
                  refine ⟨46795375263058514198484053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124787667368156037862624141 46795375263058514198484053)
                  ·
                    refine ⟨548383303863966963263485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46795375263058514198484053 548383303863966963263485)
                    ·
                      rfl

theorem cell23_3203918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3203918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203918 prefixEnd_3203918 := by exact prefixLift 3203918
  have htrace : WordTrace (prefixWord ++ tailWord_3203918) baseStart_3203918 baseEnd_3203918 := by
    simpa [prefixWord, tailWord_3203918, baseEnd_3203918] using wordTrace_append hprefix tailTrace_3203918
  have hstable : (prefixWord ++ tailWord_3203918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203918).length < 2 ^ (prefixWord ++ tailWord_3203918).sum := by decide
  have hdescent : baseEnd_3203918 < baseStart_3203918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203928 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3203928 : Nat := 118140960795 + 3203928 * 2 ^ 59
def prefixEnd_3203928 : Nat := 4983230072969 + 3 ^ 40 * 3203928 * 2
def baseEnd_3203928 : Nat := 1645155046398445850665409

theorem tailTrace_3203928 : CollatzResearch.WordTrace tailWord_3203928 prefixEnd_3203928 1645155046398445850665409 := by
  unfold tailWord_3203928
  simp only [CollatzResearch.WordTrace]
  refine ⟨58428427168361759091850219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77904569557815678789133625 58428427168361759091850219)
  ·
    refine ⟨87642640752542638637775329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58428427168361759091850219 87642640752542638637775329)
    ·
      refine ⟨65731980564406978978331497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87642640752542638637775329 65731980564406978978331497)
      ·
        refine ⟨49298985423305234233748623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65731980564406978978331497 49298985423305234233748623)
        ·
          refine ⟨73948478134957851350622935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49298985423305234233748623 73948478134957851350622935)
          ·
            refine ⟨110922717202436777025934403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73948478134957851350622935 110922717202436777025934403)
            ·
              refine ⟨166384075803655165538901605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110922717202436777025934403 166384075803655165538901605)
              ·
                refine ⟨31197014213185343538544051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166384075803655165538901605 31197014213185343538544051)
                ·
                  refine ⟨46795521319778015307816077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31197014213185343538544051 46795521319778015307816077)
                  ·
                    refine ⟨17548320494916755740431029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46795521319778015307816077 17548320494916755740431029)
                    ·
                      refine ⟨1645155046398445850665409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17548320494916755740431029 1645155046398445850665409)
                      ·
                        rfl

theorem cell23_3203928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3203928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203928 prefixEnd_3203928 := by exact prefixLift 3203928
  have htrace : WordTrace (prefixWord ++ tailWord_3203928) baseStart_3203928 baseEnd_3203928 := by
    simpa [prefixWord, tailWord_3203928, baseEnd_3203928] using wordTrace_append hprefix tailTrace_3203928
  have hstable : (prefixWord ++ tailWord_3203928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203928).length < 2 ^ (prefixWord ++ tailWord_3203928).sum := by decide
  have hdescent : baseEnd_3203928 < baseStart_3203928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203970 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3203970 : Nat := 118140960795 + 3203970 * 2 ^ 59
def prefixEnd_3203970 : Nat := 4983230072969 + 3 ^ 40 * 3203970 * 2
def baseEnd_3203970 : Nat := 1645176612585934686340217

theorem tailTrace_3203970 : CollatzResearch.WordTrace tailWord_3203970 prefixEnd_3203970 1645176612585934686340217 := by
  unfold tailWord_3203970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29214596550642839839182341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77905590801714239571152909 29214596550642839839182341)
  ·
    refine ⟨5477736853245532469846689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29214596550642839839182341 5477736853245532469846689)
    ·
      refine ⟨4108302639934149352385017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5477736853245532469846689 4108302639934149352385017)
      ·
        refine ⟨3081226979950612014288763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108302639934149352385017 3081226979950612014288763)
        ·
          refine ⟨4621840469925918021433145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081226979950612014288763 4621840469925918021433145)
          ·
            refine ⟨3466380352444438516074859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621840469925918021433145 3466380352444438516074859)
            ·
              refine ⟨5199570528666657774112289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466380352444438516074859 5199570528666657774112289)
              ·
                refine ⟨3899677896499993330584217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199570528666657774112289 3899677896499993330584217)
                ·
                  refine ⟨2924758422374994997938163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3899677896499993330584217 2924758422374994997938163)
                  ·
                    refine ⟨4387137633562492496907245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2924758422374994997938163 4387137633562492496907245)
                    ·
                      refine ⟨1645176612585934686340217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387137633562492496907245 1645176612585934686340217)
                      ·
                        rfl

theorem cell23_3203970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3203970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203970 prefixEnd_3203970 := by exact prefixLift 3203970
  have htrace : WordTrace (prefixWord ++ tailWord_3203970) baseStart_3203970 baseEnd_3203970 := by
    simpa [prefixWord, tailWord_3203970, baseEnd_3203970] using wordTrace_append hprefix tailTrace_3203970
  have hstable : (prefixWord ++ tailWord_3203970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203970).length < 2 ^ (prefixWord ++ tailWord_3203970).sum := by decide
  have hdescent : baseEnd_3203970 < baseStart_3203970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203976 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_3203976 : Nat := 118140960795 + 3203976 * 2 ^ 59
def prefixEnd_3203976 : Nat := 4983230072969 + 3 ^ 40 * 3203976 * 2
def baseEnd_3203976 : Nat := 1645179693469861662865189

theorem tailTrace_3203976 : CollatzResearch.WordTrace tailWord_3203976 prefixEnd_3203976 1645179693469861662865189 := by
  unfold tailWord_3203976
  simp only [CollatzResearch.WordTrace]
  refine ⟨58429302520274811190723891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77905736693699748254298521 58429302520274811190723891)
  ·
    refine ⟨87643953780412216786085837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58429302520274811190723891 87643953780412216786085837)
    ·
      refine ⟨32866482667654581294782189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87643953780412216786085837 32866482667654581294782189)
      ·
        refine ⟨12324931000370467985543321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32866482667654581294782189 12324931000370467985543321)
        ·
          refine ⟨9243698250277850989157491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12324931000370467985543321 9243698250277850989157491)
          ·
            refine ⟨13865547375416776483736237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243698250277850989157491 13865547375416776483736237)
            ·
              refine ⟨5199580265781291181401089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13865547375416776483736237 5199580265781291181401089)
              ·
                refine ⟨3899685199335968386050817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199580265781291181401089 3899685199335968386050817)
                ·
                  refine ⟨2924763899501976289538113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3899685199335968386050817 2924763899501976289538113)
                  ·
                    refine ⟨2193572924626482217153585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2924763899501976289538113 2193572924626482217153585)
                    ·
                      refine ⟨1645179693469861662865189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193572924626482217153585 1645179693469861662865189)
                      ·
                        rfl

theorem cell23_3203976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_3203976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3203976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3203976 prefixEnd_3203976 := by exact prefixLift 3203976
  have htrace : WordTrace (prefixWord ++ tailWord_3203976) baseStart_3203976 baseEnd_3203976 := by
    simpa [prefixWord, tailWord_3203976, baseEnd_3203976] using wordTrace_append hprefix tailTrace_3203976
  have hstable : (prefixWord ++ tailWord_3203976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203976).length < 2 ^ (prefixWord ++ tailWord_3203976).sum := by decide
  have hdescent : baseEnd_3203976 < baseStart_3203976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204032 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_3204032 : Nat := 118140960795 + 3204032 * 2 ^ 59
def prefixEnd_3204032 : Nat := 4983230072969 + 3 ^ 40 * 3204032 * 2
def baseEnd_3204032 : Nat := 1645208448386513443764931

theorem tailTrace_3204032 : CollatzResearch.WordTrace tailWord_3204032 prefixEnd_3204032 1645208448386513443764931 := by
  unfold tailWord_3204032
  simp only [CollatzResearch.WordTrace]
  refine ⟨58430323764173371972743175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77907098352231162630324233 58430323764173371972743175)
  ·
    refine ⟨87645485646260057959114763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58430323764173371972743175 87645485646260057959114763)
    ·
      refine ⟨131468228469390086938672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87645485646260057959114763 131468228469390086938672145)
      ·
        refine ⟨98601171352042565204004109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131468228469390086938672145 98601171352042565204004109)
        ·
          refine ⟨36975439257015961951501541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98601171352042565204004109 36975439257015961951501541)
          ·
            refine ⟨6932894860690492865906539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36975439257015961951501541 6932894860690492865906539)
            ·
              refine ⟨10399342291035739298859809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932894860690492865906539 10399342291035739298859809)
              ·
                refine ⟨7799506718276804474144857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10399342291035739298859809 7799506718276804474144857)
                ·
                  refine ⟨5849630038707603355608643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7799506718276804474144857 5849630038707603355608643)
                  ·
                    refine ⟨8774445058061405033412965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5849630038707603355608643 8774445058061405033412965)
                    ·
                      refine ⟨1645208448386513443764931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8774445058061405033412965 1645208448386513443764931)
                      ·
                        rfl

theorem cell23_3204032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_3204032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204032 prefixEnd_3204032 := by exact prefixLift 3204032
  have htrace : WordTrace (prefixWord ++ tailWord_3204032) baseStart_3204032 baseEnd_3204032 := by
    simpa [prefixWord, tailWord_3204032, baseEnd_3204032] using wordTrace_append hprefix tailTrace_3204032
  have hstable : (prefixWord ++ tailWord_3204032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204032).length < 2 ^ (prefixWord ++ tailWord_3204032).sum := by decide
  have hdescent : baseEnd_3204032 < baseStart_3204032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204066 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3204066 : Nat := 118140960795 + 3204066 * 2 ^ 59
def prefixEnd_3204066 : Nat := 4983230072969 + 3 ^ 40 * 3204066 * 2
def baseEnd_3204066 : Nat := 1645225906728766310739775

theorem tailTrace_3204066 : CollatzResearch.WordTrace tailWord_3204066 prefixEnd_3204066 1645225906728766310739775 := by
  unfold tailWord_3204066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215471902555891938056013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77907925073482378501482701 29215471902555891938056013)
  ·
    refine ⟨10955801963458459476771005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29215471902555891938056013 10955801963458459476771005)
    ·
      refine ⟨4108425736296922303789127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10955801963458459476771005 4108425736296922303789127)
      ·
        refine ⟨6162638604445383455683691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108425736296922303789127 6162638604445383455683691)
        ·
          refine ⟨9243957906668075183525537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162638604445383455683691 9243957906668075183525537)
          ·
            refine ⟨6932968430001056387644153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9243957906668075183525537 6932968430001056387644153)
            ·
              refine ⟨5199726322500792290733115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932968430001056387644153 5199726322500792290733115)
              ·
                refine ⟨7799589483751188436099673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199726322500792290733115 7799589483751188436099673)
                ·
                  refine ⟨5849692112813391327074755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7799589483751188436099673 5849692112813391327074755)
                  ·
                    refine ⟨8774538169220086990612133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5849692112813391327074755 8774538169220086990612133)
                    ·
                      refine ⟨1645225906728766310739775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8774538169220086990612133 1645225906728766310739775)
                      ·
                        rfl

theorem cell23_3204066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3204066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204066 prefixEnd_3204066 := by exact prefixLift 3204066
  have htrace : WordTrace (prefixWord ++ tailWord_3204066) baseStart_3204066 baseEnd_3204066 := by
    simpa [prefixWord, tailWord_3204066, baseEnd_3204066] using wordTrace_append hprefix tailTrace_3204066
  have hstable : (prefixWord ++ tailWord_3204066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204066).length < 2 ^ (prefixWord ++ tailWord_3204066).sum := by decide
  have hdescent : baseEnd_3204066 < baseStart_3204066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204084 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3204084 : Nat := 118140960795 + 3204084 * 2 ^ 59
def prefixEnd_3204084 : Nat := 4983230072969 + 3 ^ 40 * 3204084 * 2
def baseEnd_3204084 : Nat := 182803905486727471146077

theorem tailTrace_3204084 : CollatzResearch.WordTrace tailWord_3204084 prefixEnd_3204084 182803905486727471146077 := by
  unfold tailWord_3204084
  simp only [CollatzResearch.WordTrace]
  refine ⟨58431272062079178413189653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77908362749438904550919537 58431272062079178413189653)
  ·
    refine ⟨2738965877909961488118265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58431272062079178413189653 2738965877909961488118265)
    ·
      refine ⟨2054224408432471116088699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2738965877909961488118265 2054224408432471116088699)
      ·
        refine ⟨3081336612648706674133049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054224408432471116088699 3081336612648706674133049)
        ·
          refine ⟨2311002459486530005599787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3081336612648706674133049 2311002459486530005599787)
          ·
            refine ⟨3466503689229795008399681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311002459486530005599787 3466503689229795008399681)
            ·
              refine ⟨2599877766922346256299761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466503689229795008399681 2599877766922346256299761)
              ·
                refine ⟨1949908325191759692224821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599877766922346256299761 1949908325191759692224821)
                ·
                  refine ⟨182803905486727471146077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1949908325191759692224821 182803905486727471146077)
                  ·
                    rfl

theorem cell23_3204084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3204084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204084 prefixEnd_3204084 := by exact prefixLift 3204084
  have htrace : WordTrace (prefixWord ++ tailWord_3204084) baseStart_3204084 baseEnd_3204084 := by
    simpa [prefixWord, tailWord_3204084, baseEnd_3204084] using wordTrace_append hprefix tailTrace_3204084
  have hstable : (prefixWord ++ tailWord_3204084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204084).length < 2 ^ (prefixWord ++ tailWord_3204084).sum := by decide
  have hdescent : baseEnd_3204084 < baseStart_3204084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204122 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_3204122 : Nat := 118140960795 + 3204122 * 2 ^ 59
def prefixEnd_3204122 : Nat := 4983230072969 + 3 ^ 40 * 3204122 * 2
def baseEnd_3204122 : Nat := 1645254661645418091639517

theorem tailTrace_3204122 : CollatzResearch.WordTrace tailWord_3204122 prefixEnd_3204122 1645254661645418091639517 := by
  unfold tailWord_3204122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215982524505172329065655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77909286732013792877508413 29215982524505172329065655)
  ·
    refine ⟨43823973786757758493598483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29215982524505172329065655 43823973786757758493598483)
    ·
      refine ⟨65735960680136637740397725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43823973786757758493598483 65735960680136637740397725)
      ·
        refine ⟨24650985255051239152649147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65735960680136637740397725 24650985255051239152649147)
        ·
          refine ⟨36976477882576858728973721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24650985255051239152649147 36976477882576858728973721)
          ·
            refine ⟨27732358411932644046730291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36976477882576858728973721 27732358411932644046730291)
            ·
              refine ⟨41598537617898966070095437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27732358411932644046730291 41598537617898966070095437)
              ·
                refine ⟨15599451606712112276285789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41598537617898966070095437 15599451606712112276285789)
                ·
                  refine ⟨5849794352517042103607171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15599451606712112276285789 5849794352517042103607171)
                  ·
                    refine ⟨8774691528775563155410757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5849794352517042103607171 8774691528775563155410757)
                    ·
                      refine ⟨1645254661645418091639517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8774691528775563155410757 1645254661645418091639517)
                      ·
                        rfl

theorem cell23_3204122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_3204122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204122 prefixEnd_3204122 := by exact prefixLift 3204122
  have htrace : WordTrace (prefixWord ++ tailWord_3204122) baseStart_3204122 baseEnd_3204122 := by
    simpa [prefixWord, tailWord_3204122, baseEnd_3204122] using wordTrace_append hprefix tailTrace_3204122
  have hstable : (prefixWord ++ tailWord_3204122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204122).length < 2 ^ (prefixWord ++ tailWord_3204122).sum := by decide
  have hdescent : baseEnd_3204122 < baseStart_3204122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204139 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 5, 2, 2]
def baseStart_3204139 : Nat := 118140960795 + 3204139 * 2 ^ 59
def prefixEnd_3204139 : Nat := 4983230072969 + 3 ^ 40 * 3204139 * 2
def baseEnd_3204139 : Nat := 1645263390816544525126939

theorem tailTrace_3204139 : CollatzResearch.WordTrace tailWord_3204139 prefixEnd_3204139 1645263390816544525126939 := by
  unfold tailWord_3204139
  simp only [CollatzResearch.WordTrace]
  refine ⟨116864550138959101219631471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77909700092639400813087647 116864550138959101219631471)
  ·
    refine ⟨175296825208438651829447207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116864550138959101219631471 175296825208438651829447207)
    ·
      refine ⟨262945237812657977744170811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175296825208438651829447207 262945237812657977744170811)
      ·
        refine ⟨394417856718986966616256217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262945237812657977744170811 394417856718986966616256217)
        ·
          refine ⟨295813392539240224962192163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394417856718986966616256217 295813392539240224962192163)
          ·
            refine ⟨443720088808860337443288245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295813392539240224962192163 443720088808860337443288245)
            ·
              refine ⟨41598758325830656635308273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443720088808860337443288245 41598758325830656635308273)
              ·
                refine ⟨31199068744372992476481205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41598758325830656635308273 31199068744372992476481205)
                ·
                  refine ⟨2924912694784968044670113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31199068744372992476481205 2924912694784968044670113)
                  ·
                    refine ⟨2193684521088726033502585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2924912694784968044670113 2193684521088726033502585)
                    ·
                      refine ⟨1645263390816544525126939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193684521088726033502585 1645263390816544525126939)
                      ·
                        rfl

theorem cell23_3204139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 2, 2].length) (baseStart_3204139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204139 prefixEnd_3204139 := by exact prefixLift 3204139
  have htrace : WordTrace (prefixWord ++ tailWord_3204139) baseStart_3204139 baseEnd_3204139 := by
    simpa [prefixWord, tailWord_3204139, baseEnd_3204139] using wordTrace_append hprefix tailTrace_3204139
  have hstable : (prefixWord ++ tailWord_3204139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204139).length < 2 ^ (prefixWord ++ tailWord_3204139).sum := by decide
  have hdescent : baseEnd_3204139 < baseStart_3204139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204145 : List Nat := [1, 2, 2, 3, 1, 2, 12]
def baseStart_3204145 : Nat := 118140960795 + 3204145 * 2 ^ 59
def prefixEnd_3204145 : Nat := 4983230072969 + 3 ^ 40 * 3204145 * 2
def baseEnd_3204145 : Nat := 20311931749388537057431

theorem tailTrace_3204145 : CollatzResearch.WordTrace tailWord_3204145 prefixEnd_3204145 20311931749388537057431 := by
  unfold tailWord_3204145
  simp only [CollatzResearch.WordTrace]
  refine ⟨116864768976937364244349889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77909845984624909496233259 116864768976937364244349889)
  ·
    refine ⟨87648576732703023183262417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116864768976937364244349889 87648576732703023183262417)
    ·
      refine ⟨65736432549527267387446813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87648576732703023183262417 65736432549527267387446813)
      ·
        refine ⟨24651162206072725270292555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65736432549527267387446813 24651162206072725270292555)
        ·
          refine ⟨36976743309109087905438833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24651162206072725270292555 36976743309109087905438833)
          ·
            refine ⟨27732557481831815929079125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36976743309109087905438833 27732557481831815929079125)
            ·
              refine ⟨20311931749388537057431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 27732557481831815929079125 20311931749388537057431)
              ·
                rfl

theorem cell23_3204145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 12].length) (baseStart_3204145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204145 prefixEnd_3204145 := by exact prefixLift 3204145
  have htrace : WordTrace (prefixWord ++ tailWord_3204145) baseStart_3204145 baseEnd_3204145 := by
    simpa [prefixWord, tailWord_3204145, baseEnd_3204145] using wordTrace_append hprefix tailTrace_3204145
  have hstable : (prefixWord ++ tailWord_3204145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204145).length < 2 ^ (prefixWord ++ tailWord_3204145).sum := by decide
  have hdescent : baseEnd_3204145 < baseStart_3204145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204156 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_3204156 : Nat := 118140960795 + 3204156 * 2 ^ 59
def prefixEnd_3204156 : Nat := 4983230072969 + 3 ^ 40 * 3204156 * 2
def baseEnd_3204156 : Nat := 1645272119987670958614361

theorem tailTrace_3204156 : CollatzResearch.WordTrace tailWord_3204156 prefixEnd_3204156 1645272119987670958614361 := by
  unfold tailWord_3204156
  simp only [CollatzResearch.WordTrace]
  refine ⟨58432585089948756561500161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77910113453265008748666881 58432585089948756561500161)
  ·
    refine ⟨43824438817461567421125121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58432585089948756561500161 43824438817461567421125121)
    ·
      refine ⟨32868329113096175565843841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43824438817461567421125121 32868329113096175565843841)
      ·
        refine ⟨24651246834822131674382881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32868329113096175565843841 24651246834822131674382881)
        ·
          refine ⟨18488435126116598755787161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24651246834822131674382881 18488435126116598755787161)
          ·
            refine ⟨13866326344587449066840371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18488435126116598755787161 13866326344587449066840371)
            ·
              refine ⟨20799489516881173600260557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13866326344587449066840371 20799489516881173600260557)
              ·
                refine ⟨7799808568830440100097709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20799489516881173600260557 7799808568830440100097709)
                ·
                  refine ⟨2924928213311415037536641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7799808568830440100097709 2924928213311415037536641)
                  ·
                    refine ⟨2193696159983561278152481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2924928213311415037536641 2193696159983561278152481)
                    ·
                      refine ⟨1645272119987670958614361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193696159983561278152481 1645272119987670958614361)
                      ·
                        rfl

theorem cell23_3204156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_3204156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204156 prefixEnd_3204156 := by exact prefixLift 3204156
  have htrace : WordTrace (prefixWord ++ tailWord_3204156) baseStart_3204156 baseEnd_3204156 := by
    simpa [prefixWord, tailWord_3204156, baseEnd_3204156] using wordTrace_append hprefix tailTrace_3204156
  have hstable : (prefixWord ++ tailWord_3204156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204156).length < 2 ^ (prefixWord ++ tailWord_3204156).sum := by decide
  have hdescent : baseEnd_3204156 < baseStart_3204156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204166 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3204166 : Nat := 118140960795 + 3204166 * 2 ^ 59
def prefixEnd_3204166 : Nat := 4983230072969 + 3 ^ 40 * 3204166 * 2
def baseEnd_3204166 : Nat := 548425751598071973163105

theorem tailTrace_3204166 : CollatzResearch.WordTrace tailWord_3204166 prefixEnd_3204166 548425751598071973163105 := by
  unfold tailWord_3204166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652047965933165150964511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77910356606574189887242901 3652047965933165150964511)
  ·
    refine ⟨5478071948899747726446767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3652047965933165150964511 5478071948899747726446767)
    ·
      refine ⟨8217107923349621589670151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5478071948899747726446767 8217107923349621589670151)
      ·
        refine ⟨12325661885024432384505227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8217107923349621589670151 12325661885024432384505227)
        ·
          refine ⟨18488492827536648576757841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12325661885024432384505227 18488492827536648576757841)
          ·
            refine ⟨13866369620652486432568381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18488492827536648576757841 13866369620652486432568381)
            ·
              refine ⟨5199888607744682412213143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13866369620652486432568381 5199888607744682412213143)
              ·
                refine ⟨7799832911617023618319715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199888607744682412213143 7799832911617023618319715)
                ·
                  refine ⟨11699749367425535427479573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7799832911617023618319715 11699749367425535427479573)
                  ·
                    refine ⟨548425751598071973163105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11699749367425535427479573 548425751598071973163105)
                    ·
                      rfl

theorem cell23_3204166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3204166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204166 prefixEnd_3204166 := by exact prefixLift 3204166
  have htrace : WordTrace (prefixWord ++ tailWord_3204166) baseStart_3204166 baseEnd_3204166 := by
    simpa [prefixWord, tailWord_3204166, baseEnd_3204166] using wordTrace_append hprefix tailTrace_3204166
  have hstable : (prefixWord ++ tailWord_3204166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204166).length < 2 ^ (prefixWord ++ tailWord_3204166).sum := by decide
  have hdescent : baseEnd_3204166 < baseStart_3204166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204173 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_3204173 : Nat := 118140960795 + 3204173 * 2 ^ 59
def prefixEnd_3204173 : Nat := 4983230072969 + 3 ^ 40 * 3204173 * 2
def baseEnd_3204173 : Nat := 1645280849158797392101783

theorem tailTrace_3204173 : CollatzResearch.WordTrace tailWord_3204173 prefixEnd_3204173 1645280849158797392101783 := by
  unfold tailWord_3204173
  simp only [CollatzResearch.WordTrace]
  refine ⟨116865790220835925026369173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77910526813890616684246115 116865790220835925026369173)
  ·
    refine ⟨5478083916601683985611055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116865790220835925026369173 5478083916601683985611055)
    ·
      refine ⟨8217125874902525978416583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5478083916601683985611055 8217125874902525978416583)
      ·
        refine ⟨12325688812353788967624875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8217125874902525978416583 12325688812353788967624875)
        ·
          refine ⟨18488533218530683451437313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12325688812353788967624875 18488533218530683451437313)
          ·
            refine ⟨13866399913898012588577985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18488533218530683451437313 13866399913898012588577985)
            ·
              refine ⟨10399799935423509441433489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13866399913898012588577985 10399799935423509441433489)
              ·
                refine ⟨7799849951567632081075117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10399799935423509441433489 7799849951567632081075117)
                ·
                  refine ⟨2924943731837862030403169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7799849951567632081075117 2924943731837862030403169)
                  ·
                    refine ⟨2193707798878396522802377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2924943731837862030403169 2193707798878396522802377)
                    ·
                      refine ⟨1645280849158797392101783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193707798878396522802377 1645280849158797392101783)
                      ·
                        rfl

theorem cell23_3204173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_3204173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204173 prefixEnd_3204173 := by exact prefixLift 3204173
  have htrace : WordTrace (prefixWord ++ tailWord_3204173) baseStart_3204173 baseEnd_3204173 := by
    simpa [prefixWord, tailWord_3204173, baseEnd_3204173] using wordTrace_append hprefix tailTrace_3204173
  have hstable : (prefixWord ++ tailWord_3204173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204173).length < 2 ^ (prefixWord ++ tailWord_3204173).sum := by decide
  have hdescent : baseEnd_3204173 < baseStart_3204173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204206 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3204206 : Nat := 118140960795 + 3204206 * 2 ^ 59
def prefixEnd_3204206 : Nat := 4983230072969 + 3 ^ 40 * 3204206 * 2
def baseEnd_3204206 : Nat := 1645297794020395762989131

theorem tailTrace_3204206 : CollatzResearch.WordTrace tailWord_3204206 prefixEnd_3204206 1645297794020395762989131 := by
  unfold tailWord_3204206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608374228714546457790059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77911329219810914441546981 14608374228714546457790059)
  ·
    refine ⟨21912561343071819686685089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608374228714546457790059 21912561343071819686685089)
    ·
      refine ⟨16434421007303864765013817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21912561343071819686685089 16434421007303864765013817)
      ·
        refine ⟨12325815755477898573760363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16434421007303864765013817 12325815755477898573760363)
        ·
          refine ⟨18488723633216847860640545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12325815755477898573760363 18488723633216847860640545)
          ·
            refine ⟨13866542724912635895480409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18488723633216847860640545 13866542724912635895480409)
            ·
              refine ⟨10399907043684476921610307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13866542724912635895480409 10399907043684476921610307)
              ·
                refine ⟨15599860565526715382415461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10399907043684476921610307 15599860565526715382415461)
                ·
                  refine ⟨2924973856036259134202899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15599860565526715382415461 2924973856036259134202899)
                  ·
                    refine ⟨4387460784054388701304349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2924973856036259134202899 4387460784054388701304349)
                    ·
                      refine ⟨1645297794020395762989131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387460784054388701304349 1645297794020395762989131)
                      ·
                        rfl

theorem cell23_3204206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3204206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204206 prefixEnd_3204206 := by exact prefixLift 3204206
  have htrace : WordTrace (prefixWord ++ tailWord_3204206) baseStart_3204206 baseEnd_3204206 := by
    simpa [prefixWord, tailWord_3204206, baseEnd_3204206] using wordTrace_append hprefix tailTrace_3204206
  have hstable : (prefixWord ++ tailWord_3204206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204206).length < 2 ^ (prefixWord ++ tailWord_3204206).sum := by decide
  have hdescent : baseEnd_3204206 < baseStart_3204206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204233 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 1, 3, 2]
def baseStart_3204233 : Nat := 118140960795 + 3204233 * 2 ^ 59
def prefixEnd_3204233 : Nat := 4983230072969 + 3 ^ 40 * 3204233 * 2
def baseEnd_3204233 : Nat := 1645311657998067157351507

theorem tailTrace_3204233 : CollatzResearch.WordTrace tailWord_3204233 prefixEnd_3204233 1645311657998067157351507 := by
  unfold tailWord_3204233
  simp only [CollatzResearch.WordTrace]
  refine ⟨116867978600618555273553353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77911985733745703515702235 116867978600618555273553353)
  ·
    refine ⟨87650983950463916455165015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116867978600618555273553353 87650983950463916455165015)
    ·
      refine ⟨131476475925695874682747523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87650983950463916455165015 131476475925695874682747523)
      ·
        refine ⟨197214713888543812024121285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131476475925695874682747523 197214713888543812024121285)
        ·
          refine ⟨36977758854101964754522741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197214713888543812024121285 36977758854101964754522741)
          ·
            refine ⟨3466664892572059195736507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36977758854101964754522741 3466664892572059195736507)
            ·
              refine ⟨5199997338858088793604761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466664892572059195736507 5199997338858088793604761)
              ·
                refine ⟨3899998004143566595203571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199997338858088793604761 3899998004143566595203571)
                ·
                  refine ⟨5849997006215349892805357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899998004143566595203571 5849997006215349892805357)
                  ·
                    refine ⟨2193748877330756209802009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5849997006215349892805357 2193748877330756209802009)
                    ·
                      refine ⟨1645311657998067157351507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193748877330756209802009 1645311657998067157351507)
                      ·
                        rfl

theorem cell23_3204233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 3, 2].length) (baseStart_3204233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204233 prefixEnd_3204233 := by exact prefixLift 3204233
  have htrace : WordTrace (prefixWord ++ tailWord_3204233) baseStart_3204233 baseEnd_3204233 := by
    simpa [prefixWord, tailWord_3204233, baseEnd_3204233] using wordTrace_append hprefix tailTrace_3204233
  have hstable : (prefixWord ++ tailWord_3204233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204233).length < 2 ^ (prefixWord ++ tailWord_3204233).sum := by decide
  have hdescent : baseEnd_3204233 < baseStart_3204233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204250 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3204250 : Nat := 118140960795 + 3204250 * 2 ^ 59
def prefixEnd_3204250 : Nat := 4983230072969 + 3 ^ 40 * 3204250 * 2
def baseEnd_3204250 : Nat := 1645320387169193590838929

theorem tailTrace_3204250 : CollatzResearch.WordTrace tailWord_3204250 prefixEnd_3204250 1645320387169193590838929 := by
  unfold tailWord_3204250
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217149660389241794230551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77912399094371311451281469 29217149660389241794230551)
  ·
    refine ⟨43825724490583862691345827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29217149660389241794230551 43825724490583862691345827)
    ·
      refine ⟨65738586735875794037018741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43825724490583862691345827 65738586735875794037018741)
      ·
        refine ⟨6162992506488355690970507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65738586735875794037018741 6162992506488355690970507)
        ·
          refine ⟨9244488759732533536455761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162992506488355690970507 9244488759732533536455761)
          ·
            refine ⟨6933366569799400152341821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244488759732533536455761 6933366569799400152341821)
            ·
              refine ⟨2600012463674775057128183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6933366569799400152341821 2600012463674775057128183)
              ·
                refine ⟨3900018695512162585692275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600012463674775057128183 3900018695512162585692275)
                ·
                  refine ⟨5850028043268243878538413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900018695512162585692275 5850028043268243878538413)
                  ·
                    refine ⟨2193760516225591454451905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5850028043268243878538413 2193760516225591454451905)
                    ·
                      refine ⟨1645320387169193590838929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193760516225591454451905 1645320387169193590838929)
                      ·
                        rfl

theorem cell23_3204250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3204250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204250 prefixEnd_3204250 := by exact prefixLift 3204250
  have htrace : WordTrace (prefixWord ++ tailWord_3204250) baseStart_3204250 baseEnd_3204250 := by
    simpa [prefixWord, tailWord_3204250, baseEnd_3204250] using wordTrace_append hprefix tailTrace_3204250
  have hstable : (prefixWord ++ tailWord_3204250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204250).length < 2 ^ (prefixWord ++ tailWord_3204250).sum := by decide
  have hdescent : baseEnd_3204250 < baseStart_3204250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204266 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3204266 : Nat := 118140960795 + 3204266 * 2 ^ 59
def prefixEnd_3204266 : Nat := 4983230072969 + 3 ^ 40 * 3204266 * 2
def baseEnd_3204266 : Nat := 1645328602859665528238855

theorem tailTrace_3204266 : CollatzResearch.WordTrace tailWord_3204266 prefixEnd_3204266 1645328602859665528238855 := by
  unfold tailWord_3204266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217295552374750477376163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77912788139666001273003101 29217295552374750477376163)
  ·
    refine ⟨43825943328562125716064245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29217295552374750477376163 43825943328562125716064245)
    ·
      refine ⟨4108682187052699285881023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43825943328562125716064245 4108682187052699285881023)
      ·
        refine ⟨6163023280579048928821535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108682187052699285881023 6163023280579048928821535)
        ·
          refine ⟨9244534920868573393232303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163023280579048928821535 9244534920868573393232303)
          ·
            refine ⟨13866802381302860089848455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244534920868573393232303 13866802381302860089848455)
            ·
              refine ⟨20800203571954290134772683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13866802381302860089848455 20800203571954290134772683)
              ·
                refine ⟨31200305357931435202159025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20800203571954290134772683 31200305357931435202159025)
                ·
                  refine ⟨23400229018448576401619269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31200305357931435202159025 23400229018448576401619269)
                  ·
                    refine ⟨4387542940959108075303613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23400229018448576401619269 4387542940959108075303613)
                    ·
                      refine ⟨1645328602859665528238855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387542940959108075303613 1645328602859665528238855)
                      ·
                        rfl

theorem cell23_3204266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3204266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204266 prefixEnd_3204266 := by exact prefixLift 3204266
  have htrace : WordTrace (prefixWord ++ tailWord_3204266) baseStart_3204266 baseEnd_3204266 := by
    simpa [prefixWord, tailWord_3204266, baseEnd_3204266] using wordTrace_append hprefix tailTrace_3204266
  have hstable : (prefixWord ++ tailWord_3204266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204266).length < 2 ^ (prefixWord ++ tailWord_3204266).sum := by decide
  have hdescent : baseEnd_3204266 < baseStart_3204266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204279 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_3204279 : Nat := 118140960795 + 3204279 * 2 ^ 59
def prefixEnd_3204279 : Nat := 4983230072969 + 3 ^ 40 * 3204279 * 2
def baseEnd_3204279 : Nat := 1645335278108173977376295

theorem tailTrace_3204279 : CollatzResearch.WordTrace tailWord_3204279 prefixEnd_3204279 1645335278108173977376295 := by
  unfold tailWord_3204279
  simp only [CollatzResearch.WordTrace]
  refine ⟨116869656358451905129727891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77913104238967936753151927 116869656358451905129727891)
  ·
    refine ⟨175304484537677857694591837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116869656358451905129727891 175304484537677857694591837)
    ·
      refine ⟨65739181701629196635471939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175304484537677857694591837 65739181701629196635471939)
      ·
        refine ⟨98608772552443794953207909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65739181701629196635471939 98608772552443794953207909)
        ·
          refine ⟨18489144853583211553726483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98608772552443794953207909 18489144853583211553726483)
          ·
            refine ⟨27733717280374817330589725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489144853583211553726483 27733717280374817330589725)
            ·
              refine ⟨10400143980140556498971147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27733717280374817330589725 10400143980140556498971147)
              ·
                refine ⟨15600215970210834748456721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400143980140556498971147 15600215970210834748456721)
                ·
                  refine ⟨11700161977658126061342541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15600215970210834748456721 11700161977658126061342541)
                  ·
                    refine ⟨4387560741621797273003453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11700161977658126061342541 4387560741621797273003453)
                    ·
                      refine ⟨1645335278108173977376295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387560741621797273003453 1645335278108173977376295)
                      ·
                        rfl

theorem cell23_3204279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_3204279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204279 prefixEnd_3204279 := by exact prefixLift 3204279
  have htrace : WordTrace (prefixWord ++ tailWord_3204279) baseStart_3204279 baseEnd_3204279 := by
    simpa [prefixWord, tailWord_3204279, baseEnd_3204279] using wordTrace_append hprefix tailTrace_3204279
  have hstable : (prefixWord ++ tailWord_3204279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204279).length < 2 ^ (prefixWord ++ tailWord_3204279).sum := by decide
  have hdescent : baseEnd_3204279 < baseStart_3204279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204282 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_3204282 : Nat := 118140960795 + 3204282 * 2 ^ 59
def prefixEnd_3204282 : Nat := 4983230072969 + 3 ^ 40 * 3204282 * 2
def baseEnd_3204282 : Nat := 548445606183379155212927

theorem tailTrace_3204282 : CollatzResearch.WordTrace tailWord_3204282 prefixEnd_3204282 548445606183379155212927 := by
  unfold tailWord_3204282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217441444360259160521775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77913177184960691094724733 29217441444360259160521775)
  ·
    refine ⟨43826162166540388740782663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29217441444360259160521775 43826162166540388740782663)
    ·
      refine ⟨65739243249810583111173995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43826162166540388740782663 65739243249810583111173995)
      ·
        refine ⟨98608864874715874666760993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65739243249810583111173995 98608864874715874666760993)
        ·
          refine ⟨73956648656036906000070745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98608864874715874666760993 73956648656036906000070745)
          ·
            refine ⟨55467486492027679500053059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73956648656036906000070745 55467486492027679500053059)
            ·
              refine ⟨83201229738041519250079589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55467486492027679500053059 83201229738041519250079589)
              ·
                refine ⟨15600230575882784859389923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83201229738041519250079589 15600230575882784859389923)
                ·
                  refine ⟨23400345863824177289084885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15600230575882784859389923 23400345863824177289084885)
                  ·
                    refine ⟨548445606183379155212927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23400345863824177289084885 548445606183379155212927)
                    ·
                      rfl

theorem cell23_3204282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_3204282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204282 prefixEnd_3204282 := by exact prefixLift 3204282
  have htrace : WordTrace (prefixWord ++ tailWord_3204282) baseStart_3204282 baseEnd_3204282 := by
    simpa [prefixWord, tailWord_3204282, baseEnd_3204282] using wordTrace_append hprefix tailTrace_3204282
  have hstable : (prefixWord ++ tailWord_3204282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204282).length < 2 ^ (prefixWord ++ tailWord_3204282).sum := by decide
  have hdescent : baseEnd_3204282 < baseStart_3204282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204301 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3204301 : Nat := 118140960795 + 3204301 * 2 ^ 59
def prefixEnd_3204301 : Nat := 4983230072969 + 3 ^ 40 * 3204301 * 2
def baseEnd_3204301 : Nat := 1645346574682572891301195

theorem tailTrace_3204301 : CollatzResearch.WordTrace tailWord_3204301 prefixEnd_3204301 1645346574682572891301195 := by
  unfold tailWord_3204301
  simp only [CollatzResearch.WordTrace]
  refine ⟨116870458764372202887028757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77913639176248135258019171 116870458764372202887028757)
  ·
    refine ⟨5478302754579947010329473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116870458764372202887028757 5478302754579947010329473)
    ·
      refine ⟨4108727065934960257747105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5478302754579947010329473 4108727065934960257747105)
      ·
        refine ⟨3081545299451220193310329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108727065934960257747105 3081545299451220193310329)
        ·
          refine ⟨2311158974588415144982747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3081545299451220193310329 2311158974588415144982747)
          ·
            refine ⟨3466738461882622717474121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311158974588415144982747 3466738461882622717474121)
            ·
              refine ⟨2600053846411967038105591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466738461882622717474121 2600053846411967038105591)
              ·
                refine ⟨3900080769617950557158387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600053846411967038105591 3900080769617950557158387)
                ·
                  refine ⟨5850121154426925835737581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900080769617950557158387 5850121154426925835737581)
                  ·
                    refine ⟨2193795432910097188401593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5850121154426925835737581 2193795432910097188401593)
                    ·
                      refine ⟨1645346574682572891301195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193795432910097188401593 1645346574682572891301195)
                      ·
                        rfl

theorem cell23_3204301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3204301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204301 prefixEnd_3204301 := by exact prefixLift 3204301
  have htrace : WordTrace (prefixWord ++ tailWord_3204301) baseStart_3204301 baseEnd_3204301 := by
    simpa [prefixWord, tailWord_3204301, baseEnd_3204301] using wordTrace_append hprefix tailTrace_3204301
  have hstable : (prefixWord ++ tailWord_3204301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204301).length < 2 ^ (prefixWord ++ tailWord_3204301).sum := by decide
  have hdescent : baseEnd_3204301 < baseStart_3204301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204319 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3204319 : Nat := 118140960795 + 3204319 * 2 ^ 59
def prefixEnd_3204319 : Nat := 4983230072969 + 3 ^ 40 * 3204319 * 2
def baseEnd_3204319 : Nat := 1645355817334353820876111

theorem tailTrace_3204319 : CollatzResearch.WordTrace tailWord_3204319 prefixEnd_3204319 1645355817334353820876111 := by
  unfold tailWord_3204319
  simp only [CollatzResearch.WordTrace]
  refine ⟨116871115278306991961184011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77914076852204661307456007 116871115278306991961184011)
  ·
    refine ⟨175306672917460487941776017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116871115278306991961184011 175306672917460487941776017)
    ·
      refine ⟨131480004688095365956332013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175306672917460487941776017 131480004688095365956332013)
      ·
        refine ⟨49305001758035762233624505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131480004688095365956332013 49305001758035762233624505)
        ·
          refine ⟨36978751318526821675218379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49305001758035762233624505 36978751318526821675218379)
          ·
            refine ⟨55468126977790232512827569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36978751318526821675218379 55468126977790232512827569)
            ·
              refine ⟨41601095233342674384620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55468126977790232512827569 41601095233342674384620677)
              ·
                refine ⟨7800205356251751447116377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41601095233342674384620677 7800205356251751447116377)
                ·
                  refine ⟨5850154017188813585337283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800205356251751447116377 5850154017188813585337283)
                  ·
                    refine ⟨8775231025783220378005925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850154017188813585337283 8775231025783220378005925)
                    ·
                      refine ⟨1645355817334353820876111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8775231025783220378005925 1645355817334353820876111)
                      ·
                        rfl

theorem cell23_3204319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3204319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204319 prefixEnd_3204319 := by exact prefixLift 3204319
  have htrace : WordTrace (prefixWord ++ tailWord_3204319) baseStart_3204319 baseEnd_3204319 := by
    simpa [prefixWord, tailWord_3204319, baseEnd_3204319] using wordTrace_append hprefix tailTrace_3204319
  have hstable : (prefixWord ++ tailWord_3204319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204319).length < 2 ^ (prefixWord ++ tailWord_3204319).sum := by decide
  have hdescent : baseEnd_3204319 < baseStart_3204319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204339 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3]
def baseStart_3204339 : Nat := 118140960795 + 3204339 * 2 ^ 59
def prefixEnd_3204339 : Nat := 4983230072969 + 3 ^ 40 * 3204339 * 2
def baseEnd_3204339 : Nat := 1645366086947443742626019

theorem tailTrace_3204339 : CollatzResearch.WordTrace tailWord_3204339 prefixEnd_3204339 1645366086947443742626019 := by
  unfold tailWord_3204339
  simp only [CollatzResearch.WordTrace]
  refine ⟨116871844738234535376912071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77914563158823023584608047 116871844738234535376912071)
  ·
    refine ⟨175307767107351803065368107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116871844738234535376912071 175307767107351803065368107)
    ·
      refine ⟨262961650661027704598052161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175307767107351803065368107 262961650661027704598052161)
      ·
        refine ⟨197221237995770778448539121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262961650661027704598052161 197221237995770778448539121)
        ·
          refine ⟨147915928496828083836404341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197221237995770778448539121 147915928496828083836404341)
          ·
            refine ⟨13867118296577632859662907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147915928496828083836404341 13867118296577632859662907)
            ·
              refine ⟨20800677444866449289494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13867118296577632859662907 20800677444866449289494361)
              ·
                refine ⟨15600508083649836967120771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20800677444866449289494361 15600508083649836967120771)
                ·
                  refine ⟨23400762125474755450681157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15600508083649836967120771 23400762125474755450681157)
                  ·
                    refine ⟨4387642898526516647002717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23400762125474755450681157 4387642898526516647002717)
                    ·
                      refine ⟨1645366086947443742626019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387642898526516647002717 1645366086947443742626019)
                      ·
                        rfl

theorem cell23_3204339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_3204339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204339 prefixEnd_3204339 := by exact prefixLift 3204339
  have htrace : WordTrace (prefixWord ++ tailWord_3204339) baseStart_3204339 baseEnd_3204339 := by
    simpa [prefixWord, tailWord_3204339, baseEnd_3204339] using wordTrace_append hprefix tailTrace_3204339
  have hstable : (prefixWord ++ tailWord_3204339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204339).length < 2 ^ (prefixWord ++ tailWord_3204339).sum := by decide
  have hdescent : baseEnd_3204339 < baseStart_3204339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204356 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3204356 : Nat := 118140960795 + 3204356 * 2 ^ 59
def prefixEnd_3204356 : Nat := 4983230072969 + 3 ^ 40 * 3204356 * 2
def baseEnd_3204356 : Nat := 1645374816118570176113441

theorem tailTrace_3204356 : CollatzResearch.WordTrace tailWord_3204356 prefixEnd_3204356 1645374816118570176113441 := by
  unfold tailWord_3204356
  simp only [CollatzResearch.WordTrace]
  refine ⟨58436232389586473640140461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77914976519448631520187281 58436232389586473640140461)
  ·
    refine ⟨21913587146094927615052673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58436232389586473640140461 21913587146094927615052673)
    ·
      refine ⟨16435190359571195711289505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21913587146094927615052673 16435190359571195711289505)
      ·
        refine ⟨12326392769678396783467129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16435190359571195711289505 12326392769678396783467129)
        ·
          refine ⟨9244794577258797587600347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12326392769678396783467129 9244794577258797587600347)
          ·
            refine ⟨13867191865888196381400521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244794577258797587600347 13867191865888196381400521)
            ·
              refine ⟨10400393899416147286050391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13867191865888196381400521 10400393899416147286050391)
              ·
                refine ⟨15600590849124220929075587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400393899416147286050391 15600590849124220929075587)
                ·
                  refine ⟨23400886273686331393613381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15600590849124220929075587 23400886273686331393613381)
                  ·
                    refine ⟨4387666176316187136302509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23400886273686331393613381 4387666176316187136302509)
                    ·
                      refine ⟨1645374816118570176113441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387666176316187136302509 1645374816118570176113441)
                      ·
                        rfl

theorem cell23_3204356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3204356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204356 prefixEnd_3204356 := by exact prefixLift 3204356
  have htrace : WordTrace (prefixWord ++ tailWord_3204356) baseStart_3204356 baseEnd_3204356 := by
    simpa [prefixWord, tailWord_3204356, baseEnd_3204356] using wordTrace_append hprefix tailTrace_3204356
  have hstable : (prefixWord ++ tailWord_3204356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204356).length < 2 ^ (prefixWord ++ tailWord_3204356).sum := by decide
  have hdescent : baseEnd_3204356 < baseStart_3204356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204363 : List Nat := [1, 1, 1, 1, 5, 3, 3, 3, 1, 4]
def baseStart_3204363 : Nat := 118140960795 + 3204363 * 2 ^ 59
def prefixEnd_3204363 : Nat := 4983230072969 + 3 ^ 40 * 3204363 * 2
def baseEnd_3204363 : Nat := 548459470161050549575303

theorem tailTrace_3204363 : CollatzResearch.WordTrace tailWord_3204363 prefixEnd_3204363 548459470161050549575303 := by
  unfold tailWord_3204363
  simp only [CollatzResearch.WordTrace]
  refine ⟨116872720090147587475785743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77915146726765058317190495 116872720090147587475785743)
  ·
    refine ⟨175309080135221381213678615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116872720090147587475785743 175309080135221381213678615)
    ·
      refine ⟨262963620202832071820517923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175309080135221381213678615 262963620202832071820517923)
      ·
        refine ⟨394445430304248107730776885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262963620202832071820517923 394445430304248107730776885)
        ·
          refine ⟨36979259091023260099760333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394445430304248107730776885 36979259091023260099760333)
          ·
            refine ⟨13867222159133722537410125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36979259091023260099760333 13867222159133722537410125)
            ·
              refine ⟨5200208309675145951528797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13867222159133722537410125 5200208309675145951528797)
              ·
                refine ⟨1950078116128179731823299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5200208309675145951528797 1950078116128179731823299)
                ·
                  refine ⟨2925117174192269597734949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950078116128179731823299 2925117174192269597734949)
                  ·
                    refine ⟨548459470161050549575303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925117174192269597734949 548459470161050549575303)
                    ·
                      rfl

theorem cell23_3204363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3, 1, 4].length) (baseStart_3204363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204363 prefixEnd_3204363 := by exact prefixLift 3204363
  have htrace : WordTrace (prefixWord ++ tailWord_3204363) baseStart_3204363 baseEnd_3204363 := by
    simpa [prefixWord, tailWord_3204363, baseEnd_3204363] using wordTrace_append hprefix tailTrace_3204363
  have hstable : (prefixWord ++ tailWord_3204363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204363).length < 2 ^ (prefixWord ++ tailWord_3204363).sum := by decide
  have hdescent : baseEnd_3204363 < baseStart_3204363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204370 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3204370 : Nat := 118140960795 + 3204370 * 2 ^ 59
def prefixEnd_3204370 : Nat := 4983230072969 + 3 ^ 40 * 3204370 * 2
def baseEnd_3204370 : Nat := 1645382004847733121338377

theorem tailTrace_3204370 : CollatzResearch.WordTrace tailWord_3204370 prefixEnd_3204370 1645382004847733121338377 := by
  unfold tailWord_3204370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218243850280556917822641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77915316934081485114193709 29218243850280556917822641)
  ·
    refine ⟨21913682887710417688366981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29218243850280556917822641 21913682887710417688366981)
    ·
      refine ⟨4108815541445703316568809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21913682887710417688366981 4108815541445703316568809)
      ·
        refine ⟨3081611656084277487426607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108815541445703316568809 3081611656084277487426607)
        ·
          refine ⟨4622417484126416231139911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081611656084277487426607 4622417484126416231139911)
          ·
            refine ⟨6933626226189624346709867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4622417484126416231139911 6933626226189624346709867)
            ·
              refine ⟨10400439339284436520064801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933626226189624346709867 10400439339284436520064801)
              ·
                refine ⟨7800329504463327390048601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10400439339284436520064801 7800329504463327390048601)
                ·
                  refine ⟨5850247128347495542536451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800329504463327390048601 5850247128347495542536451)
                  ·
                    refine ⟨8775370692521243313804677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850247128347495542536451 8775370692521243313804677)
                    ·
                      refine ⟨1645382004847733121338377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8775370692521243313804677 1645382004847733121338377)
                      ·
                        rfl

theorem cell23_3204370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3204370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204370 prefixEnd_3204370 := by exact prefixLift 3204370
  have htrace : WordTrace (prefixWord ++ tailWord_3204370) baseStart_3204370 baseEnd_3204370 := by
    simpa [prefixWord, tailWord_3204370, baseEnd_3204370] using wordTrace_append hprefix tailTrace_3204370
  have hstable : (prefixWord ++ tailWord_3204370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204370).length < 2 ^ (prefixWord ++ tailWord_3204370).sum := by decide
  have hdescent : baseEnd_3204370 < baseStart_3204370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204396 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_3204396 : Nat := 118140960795 + 3204396 * 2 ^ 59
def prefixEnd_3204396 : Nat := 4983230072969 + 3 ^ 40 * 3204396 * 2
def baseEnd_3204396 : Nat := 1645395355344750019613257

theorem tailTrace_3204396 : CollatzResearch.WordTrace tailWord_3204396 prefixEnd_3204396 1645395355344750019613257 := by
  unfold tailWord_3204396
  simp only [CollatzResearch.WordTrace]
  refine ⟨58436961849514017055868521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77915949132685356074491361 58436961849514017055868521)
  ·
    refine ⟨43827721387135512791901391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58436961849514017055868521 43827721387135512791901391)
    ·
      refine ⟨65741582080703269187852087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43827721387135512791901391 65741582080703269187852087)
      ·
        refine ⟨98612373121054903781778131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65741582080703269187852087 98612373121054903781778131)
        ·
          refine ⟨147918559681582355672667197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98612373121054903781778131 147918559681582355672667197)
          ·
            refine ⟨55469459880593383377250199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147918559681582355672667197 55469459880593383377250199)
            ·
              refine ⟨83204189820890075065875299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55469459880593383377250199 83204189820890075065875299)
              ·
                refine ⟨124806284731335112598812949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83204189820890075065875299 124806284731335112598812949)
                ·
                  refine ⟨5850294596781333403069357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124806284731335112598812949 5850294596781333403069357)
                  ·
                    refine ⟨2193860473793000026151009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5850294596781333403069357 2193860473793000026151009)
                    ·
                      refine ⟨1645395355344750019613257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193860473793000026151009 1645395355344750019613257)
                      ·
                        rfl

theorem cell23_3204396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_3204396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204396 prefixEnd_3204396 := by exact prefixLift 3204396
  have htrace : WordTrace (prefixWord ++ tailWord_3204396) baseStart_3204396 baseEnd_3204396 := by
    simpa [prefixWord, tailWord_3204396, baseEnd_3204396] using wordTrace_append hprefix tailTrace_3204396
  have hstable : (prefixWord ++ tailWord_3204396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204396).length < 2 ^ (prefixWord ++ tailWord_3204396).sum := by decide
  have hdescent : baseEnd_3204396 < baseStart_3204396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204423 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 1, 5]
def baseStart_3204423 : Nat := 118140960795 + 3204423 * 2 ^ 59
def prefixEnd_3204423 : Nat := 4983230072969 + 3 ^ 40 * 3204423 * 2
def baseEnd_3204423 : Nat := 548469739774140471325211

theorem tailTrace_3204423 : CollatzResearch.WordTrace tailWord_3204423 prefixEnd_3204423 548469739774140471325211 := by
  unfold tailWord_3204423
  simp only [CollatzResearch.WordTrace]
  refine ⟨116874908469930217722969923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77916605646620145148646615 116874908469930217722969923)
  ·
    refine ⟨175312362704895326584454885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116874908469930217722969923 175312362704895326584454885)
    ·
      refine ⟨32871068007167873734585291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175312362704895326584454885 32871068007167873734585291)
      ·
        refine ⟨49306602010751810601877937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32871068007167873734585291 49306602010751810601877937)
        ·
          refine ⟨36979951508063857951408453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49306602010751810601877937 36979951508063857951408453)
          ·
            refine ⟨6933740907761973365889085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36979951508063857951408453 6933740907761973365889085)
            ·
              refine ⟨2600152840410740012208407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6933740907761973365889085 2600152840410740012208407)
              ·
                refine ⟨3900229260616110018312611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600152840410740012208407 3900229260616110018312611)
                ·
                  refine ⟨5850343890924165027468917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900229260616110018312611 5850343890924165027468917)
                  ·
                    refine ⟨548469739774140471325211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5850343890924165027468917 548469739774140471325211)
                    ·
                      rfl

theorem cell23_3204423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_3204423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204423 prefixEnd_3204423 := by exact prefixLift 3204423
  have htrace : WordTrace (prefixWord ++ tailWord_3204423) baseStart_3204423 baseEnd_3204423 := by
    simpa [prefixWord, tailWord_3204423, baseEnd_3204423] using wordTrace_append hprefix tailTrace_3204423
  have hstable : (prefixWord ++ tailWord_3204423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204423).length < 2 ^ (prefixWord ++ tailWord_3204423).sum := by decide
  have hdescent : baseEnd_3204423 < baseStart_3204423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204426 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3204426 : Nat := 118140960795 + 3204426 * 2 ^ 59
def prefixEnd_3204426 : Nat := 4983230072969 + 3 ^ 40 * 3204426 * 2
def baseEnd_3204426 : Nat := 1645410759764384902238119

theorem tailTrace_3204426 : CollatzResearch.WordTrace tailWord_3204426 prefixEnd_3204426 1645410759764384902238119 := by
  unfold tailWord_3204426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218754472229837308832283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77916678592612899490219421 29218754472229837308832283)
  ·
    refine ⟨43828131708344755963248425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29218754472229837308832283 43828131708344755963248425)
    ·
      refine ⟨32871098781258566972436319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43828131708344755963248425 32871098781258566972436319)
      ·
        refine ⟨49306648171887850458654479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32871098781258566972436319 49306648171887850458654479)
        ·
          refine ⟨73959972257831775687981719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49306648171887850458654479 73959972257831775687981719)
          ·
            refine ⟨110939958386747663531972579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73959972257831775687981719 110939958386747663531972579)
            ·
              refine ⟨166409937580121495297958869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110939958386747663531972579 166409937580121495297958869)
              ·
                refine ⟨3900232912034097546045911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166409937580121495297958869 3900232912034097546045911)
                ·
                  refine ⟨5850349368051146319068867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900232912034097546045911 5850349368051146319068867)
                  ·
                    refine ⟨8775524052076719478603301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850349368051146319068867 8775524052076719478603301)
                    ·
                      refine ⟨1645410759764384902238119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8775524052076719478603301 1645410759764384902238119)
                      ·
                        rfl

theorem cell23_3204426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3204426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204426 prefixEnd_3204426 := by exact prefixLift 3204426
  have htrace : WordTrace (prefixWord ++ tailWord_3204426) baseStart_3204426 baseEnd_3204426 := by
    simpa [prefixWord, tailWord_3204426, baseEnd_3204426] using wordTrace_append hprefix tailTrace_3204426
  have hstable : (prefixWord ++ tailWord_3204426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204426).length < 2 ^ (prefixWord ++ tailWord_3204426).sum := by decide
  have hdescent : baseEnd_3204426 < baseStart_3204426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204437 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3204437 : Nat := 118140960795 + 3204437 * 2 ^ 59
def prefixEnd_3204437 : Nat := 4983230072969 + 3 ^ 40 * 3204437 * 2
def baseEnd_3204437 : Nat := 1645416408051584359200569

theorem tailTrace_3204437 : CollatzResearch.WordTrace tailWord_3204437 prefixEnd_3204437 1645416408051584359200569 := by
  unfold tailWord_3204437
  simp only [CollatzResearch.WordTrace]
  refine ⟨116875419091879498113979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77916946061252998742653043 116875419091879498113979565)
  ·
    refine ⟨43828282159454811792742337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116875419091879498113979565 43828282159454811792742337)
    ·
      refine ⟨32871211619591108844556753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43828282159454811792742337 32871211619591108844556753)
      ·
        refine ⟨24653408714693331633417565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32871211619591108844556753 24653408714693331633417565)
        ·
          refine ⟨9245028268009999362531587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24653408714693331633417565 9245028268009999362531587)
          ·
            refine ⟨13867542402014999043797381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245028268009999362531587 13867542402014999043797381)
            ·
              refine ⟨2600164200377812320712009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13867542402014999043797381 2600164200377812320712009)
              ·
                refine ⟨1950123150283359240534007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2600164200377812320712009 1950123150283359240534007)
                ·
                  refine ⟨2925184725425038860801011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950123150283359240534007 2925184725425038860801011)
                  ·
                    refine ⟨4387777088137558291201517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2925184725425038860801011 4387777088137558291201517)
                    ·
                      refine ⟨1645416408051584359200569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387777088137558291201517 1645416408051584359200569)
                      ·
                        rfl

theorem cell23_3204437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3204437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204437 prefixEnd_3204437 := by exact prefixLift 3204437
  have htrace : WordTrace (prefixWord ++ tailWord_3204437) baseStart_3204437 baseEnd_3204437 := by
    simpa [prefixWord, tailWord_3204437, baseEnd_3204437] using wordTrace_append hprefix tailTrace_3204437
  have hstable : (prefixWord ++ tailWord_3204437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204437).length < 2 ^ (prefixWord ++ tailWord_3204437).sum := by decide
  have hdescent : baseEnd_3204437 < baseStart_3204437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204460 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_3204460 : Nat := 118140960795 + 3204460 * 2 ^ 59
def prefixEnd_3204460 : Nat := 4983230072969 + 3 ^ 40 * 3204460 * 2
def baseEnd_3204460 : Nat := 1645428218106637769212963

theorem tailTrace_3204460 : CollatzResearch.WordTrace tailWord_3204460 prefixEnd_3204460 1645428218106637769212963 := by
  unfold tailWord_3204460
  simp only [CollatzResearch.WordTrace]
  refine ⟨58438128985398086521033417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77917505313864115361377889 58438128985398086521033417)
  ·
    refine ⟨43828596739048564890775063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58438128985398086521033417 43828596739048564890775063)
    ·
      refine ⟨65742895108572847336162595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43828596739048564890775063 65742895108572847336162595)
      ·
        refine ⟨98614342662859271004243893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65742895108572847336162595 98614342662859271004243893)
        ·
          refine ⟨9245094624643056656647865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98614342662859271004243893 9245094624643056656647865)
          ·
            refine ⟨6933820968482292492485899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9245094624643056656647865 6933820968482292492485899)
            ·
              refine ⟨10400731452723438738728849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933820968482292492485899 10400731452723438738728849)
              ·
                refine ⟨7800548589542579054046637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10400731452723438738728849 7800548589542579054046637)
                ·
                  refine ⟨2925205721078467145267489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7800548589542579054046637 2925205721078467145267489)
                  ·
                    refine ⟨2193904290808850358950617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2925205721078467145267489 2193904290808850358950617)
                    ·
                      refine ⟨1645428218106637769212963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193904290808850358950617 1645428218106637769212963)
                      ·
                        rfl

theorem cell23_3204460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_3204460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204460 prefixEnd_3204460 := by exact prefixLift 3204460
  have htrace : WordTrace (prefixWord ++ tailWord_3204460) baseStart_3204460 baseEnd_3204460 := by
    simpa [prefixWord, tailWord_3204460, baseEnd_3204460] using wordTrace_append hprefix tailTrace_3204460
  have hstable : (prefixWord ++ tailWord_3204460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204460).length < 2 ^ (prefixWord ++ tailWord_3204460).sum := by decide
  have hdescent : baseEnd_3204460 < baseStart_3204460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204466 : List Nat := [3, 2, 1, 2, 1, 2, 5, 7]
def baseStart_3204466 : Nat := 118140960795 + 3204466 * 2 ^ 59
def prefixEnd_3204466 : Nat := 4983230072969 + 3 ^ 40 * 3204466 * 2
def baseEnd_3204466 : Nat := 60941899962613509101405

theorem tailTrace_3204466 : CollatzResearch.WordTrace tailWord_3204466 prefixEnd_3204466 60941899962613509101405 := by
  unfold tailWord_3204466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29219119202193609016696313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77917651205849624044523501 29219119202193609016696313)
  ·
    refine ⟨21914339401645206762522235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29219119202193609016696313 21914339401645206762522235)
    ·
      refine ⟨32871509102467810143783353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914339401645206762522235 32871509102467810143783353)
      ·
        refine ⟨24653631826850857607837515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32871509102467810143783353 24653631826850857607837515)
        ·
          refine ⟨36980447740276286411756273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24653631826850857607837515 36980447740276286411756273)
          ·
            refine ⟨27735335805207214808817205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36980447740276286411756273 27735335805207214808817205)
            ·
              refine ⟨2600187731738176388326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27735335805207214808817205 2600187731738176388326613)
              ·
                refine ⟨60941899962613509101405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2600187731738176388326613 60941899962613509101405)
                ·
                  rfl

theorem cell23_3204466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 7].length) (baseStart_3204466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204466 prefixEnd_3204466 := by exact prefixLift 3204466
  have htrace : WordTrace (prefixWord ++ tailWord_3204466) baseStart_3204466 baseEnd_3204466 := by
    simpa [prefixWord, tailWord_3204466, baseEnd_3204466] using wordTrace_append hprefix tailTrace_3204466
  have hstable : (prefixWord ++ tailWord_3204466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204466).length < 2 ^ (prefixWord ++ tailWord_3204466).sum := by decide
  have hdescent : baseEnd_3204466 < baseStart_3204466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204476 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_3204476 : Nat := 118140960795 + 3204476 * 2 ^ 59
def prefixEnd_3204476 : Nat := 4983230072969 + 3 ^ 40 * 3204476 * 2
def baseEnd_3204476 : Nat := 1645436433797109706612889

theorem tailTrace_3204476 : CollatzResearch.WordTrace tailWord_3204476 prefixEnd_3204476 1645436433797109706612889 := by
  unfold tailWord_3204476
  simp only [CollatzResearch.WordTrace]
  refine ⟨58438420769369103887324641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77917894359158805183099521 58438420769369103887324641)
  ·
    refine ⟨43828815577026827915493481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58438420769369103887324641 43828815577026827915493481)
    ·
      refine ⟨32871611682770120936620111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43828815577026827915493481 32871611682770120936620111)
      ·
        refine ⟨49307417524155181404930167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32871611682770120936620111 49307417524155181404930167)
        ·
          refine ⟨73961126286232772107395251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49307417524155181404930167 73961126286232772107395251)
          ·
            refine ⟨110941689429349158161092877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73961126286232772107395251 110941689429349158161092877)
            ·
              refine ⟨41603133536005934310409829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110941689429349158161092877 41603133536005934310409829)
              ·
                refine ⟨7800587538001112683201843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41603133536005934310409829 7800587538001112683201843)
                ·
                  refine ⟨11700881307001669024802765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7800587538001112683201843 11700881307001669024802765)
                  ·
                    refine ⟨4387830490125625884301037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11700881307001669024802765 4387830490125625884301037)
                    ·
                      refine ⟨1645436433797109706612889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4387830490125625884301037 1645436433797109706612889)
                      ·
                        rfl

theorem cell23_3204476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_3204476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204476 prefixEnd_3204476 := by exact prefixLift 3204476
  have htrace : WordTrace (prefixWord ++ tailWord_3204476) baseStart_3204476 baseEnd_3204476 := by
    simpa [prefixWord, tailWord_3204476, baseEnd_3204476] using wordTrace_append hprefix tailTrace_3204476
  have hstable : (prefixWord ++ tailWord_3204476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204476).length < 2 ^ (prefixWord ++ tailWord_3204476).sum := by decide
  have hdescent : baseEnd_3204476 < baseStart_3204476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204477 : List Nat := [1, 4, 1, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_3204477 : Nat := 118140960795 + 3204477 * 2 ^ 59
def prefixEnd_3204477 : Nat := 4983230072969 + 3 ^ 40 * 3204477 * 2
def baseEnd_3204477 : Nat := 1645436947277764202700385

theorem tailTrace_3204477 : CollatzResearch.WordTrace tailWord_3204477 prefixEnd_3204477 1645436947277764202700385 := by
  unfold tailWord_3204477
  simp only [CollatzResearch.WordTrace]
  refine ⟨116876878011734584945435685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77917918674489723296957123 116876878011734584945435685)
  ·
    refine ⟨21914414627200234677269191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116876878011734584945435685 21914414627200234677269191)
    ·
      refine ⟨32871621940800352015903787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914414627200234677269191 32871621940800352015903787)
      ·
        refine ⟨49307432911200528023855681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32871621940800352015903787 49307432911200528023855681)
        ·
          refine ⟨36980574683400396017891761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49307432911200528023855681 36980574683400396017891761)
          ·
            refine ⟨27735431012550297013418821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36980574683400396017891761 27735431012550297013418821)
            ·
              refine ⟨5200393314853180690016029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27735431012550297013418821 5200393314853180690016029)
              ·
                refine ⟨1950147493069942758756011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5200393314853180690016029 1950147493069942758756011)
                ·
                  refine ⟨2925221239604914138134017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950147493069942758756011 2925221239604914138134017)
                  ·
                    refine ⟨2193915929703685603600513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2925221239604914138134017 2193915929703685603600513)
                    ·
                      refine ⟨1645436947277764202700385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2193915929703685603600513 1645436947277764202700385)
                      ·
                        rfl

theorem cell23_3204477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_3204477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204477 prefixEnd_3204477 := by exact prefixLift 3204477
  have htrace : WordTrace (prefixWord ++ tailWord_3204477) baseStart_3204477 baseEnd_3204477 := by
    simpa [prefixWord, tailWord_3204477, baseEnd_3204477] using wordTrace_append hprefix tailTrace_3204477
  have hstable : (prefixWord ++ tailWord_3204477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204477).length < 2 ^ (prefixWord ++ tailWord_3204477).sum := by decide
  have hdescent : baseEnd_3204477 < baseStart_3204477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204614 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3204614 : Nat := 118140960795 + 3204614 * 2 ^ 59
def prefixEnd_3204614 : Nat := 4983230072969 + 3 ^ 40 * 3204614 * 2
def baseEnd_3204614 : Nat := 1645507294127430166687255

theorem tailTrace_3204614 : CollatzResearch.WordTrace tailWord_3204614 prefixEnd_3204614 1645507294127430166687255 := by
  unfold tailWord_3204614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652558587882445541974153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77921249874825504895448597 3652558587882445541974153)
  ·
    refine ⟨2739418940911834156480615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3652558587882445541974153 2739418940911834156480615)
    ·
      refine ⟨4109128411367751234720923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2739418940911834156480615 4109128411367751234720923)
      ·
        refine ⟨6163692617051626852081385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4109128411367751234720923 6163692617051626852081385)
        ·
          refine ⟨4622769462788720139061039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6163692617051626852081385 4622769462788720139061039)
          ·
            refine ⟨6934154194183080208591559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4622769462788720139061039 6934154194183080208591559)
            ·
              refine ⟨10401231291274620312887339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934154194183080208591559 10401231291274620312887339)
              ·
                refine ⟨15601846936911930469331009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401231291274620312887339 15601846936911930469331009)
                ·
                  refine ⟨11701385202683947851998257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15601846936911930469331009 11701385202683947851998257)
                  ·
                    refine ⟨8776038902012960888998693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11701385202683947851998257 8776038902012960888998693)
                    ·
                      refine ⟨1645507294127430166687255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8776038902012960888998693 1645507294127430166687255)
                      ·
                        rfl

theorem cell23_3204614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3204614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204614 prefixEnd_3204614 := by exact prefixLift 3204614
  have htrace : WordTrace (prefixWord ++ tailWord_3204614) baseStart_3204614 baseEnd_3204614 := by
    simpa [prefixWord, tailWord_3204614, baseEnd_3204614] using wordTrace_append hprefix tailTrace_3204614
  have hstable : (prefixWord ++ tailWord_3204614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204614).length < 2 ^ (prefixWord ++ tailWord_3204614).sum := by decide
  have hdescent : baseEnd_3204614 < baseStart_3204614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204640 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3204640 : Nat := 118140960795 + 3204640 * 2 ^ 59
def prefixEnd_3204640 : Nat := 4983230072969 + 3 ^ 40 * 3204640 * 2
def baseEnd_3204640 : Nat := 1645520644624447064962135

theorem tailTrace_3204640 : CollatzResearch.WordTrace tailWord_3204640 prefixEnd_3204640 1645520644624447064962135 := by
  unfold tailWord_3204640
  simp only [CollatzResearch.WordTrace]
  refine ⟨58441411555072031891809687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77921882073429375855746249 58441411555072031891809687)
  ·
    refine ⟨87662117332608047837714531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58441411555072031891809687 87662117332608047837714531)
    ·
      refine ⟨131493175998912071756571797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87662117332608047837714531 131493175998912071756571797)
      ·
        refine ⟨6163742624949003363589303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131493175998912071756571797 6163742624949003363589303)
        ·
          refine ⟨9245613937423505045383955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163742624949003363589303 9245613937423505045383955)
          ·
            refine ⟨13868420906135257568075933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245613937423505045383955 13868420906135257568075933)
            ·
              refine ⟨5200657839800721588028475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13868420906135257568075933 5200657839800721588028475)
              ·
                refine ⟨7800986759701082382042713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5200657839800721588028475 7800986759701082382042713)
                ·
                  refine ⟨5850740069775811786532035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800986759701082382042713 5850740069775811786532035)
                  ·
                    refine ⟨8776110104663717679798053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850740069775811786532035 8776110104663717679798053)
                    ·
                      refine ⟨1645520644624447064962135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8776110104663717679798053 1645520644624447064962135)
                      ·
                        rfl

theorem cell23_3204640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3204640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204640 prefixEnd_3204640 := by exact prefixLift 3204640
  have htrace : WordTrace (prefixWord ++ tailWord_3204640) baseStart_3204640 baseEnd_3204640 := by
    simpa [prefixWord, tailWord_3204640, baseEnd_3204640] using wordTrace_append hprefix tailTrace_3204640
  have hstable : (prefixWord ++ tailWord_3204640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204640).length < 2 ^ (prefixWord ++ tailWord_3204640).sum := by decide
  have hdescent : baseEnd_3204640 < baseStart_3204640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204663 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 6]
def baseStart_3204663 : Nat := 118140960795 + 3204663 * 2 ^ 59
def prefixEnd_3204663 : Nat := 4983230072969 + 3 ^ 40 * 3204663 * 2
def baseEnd_3204663 : Nat := 182836939408833386108281

theorem tailTrace_3204663 : CollatzResearch.WordTrace tailWord_3204663 prefixEnd_3204663 182836939408833386108281 := by
  unfold tailWord_3204663
  simp only [CollatzResearch.WordTrace]
  refine ⟨116883661989060738711706643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77922441326040492474471095 116883661989060738711706643)
  ·
    refine ⟨175325492983591108067559965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116883661989060738711706643 175325492983591108067559965)
    ·
      refine ⟨65747059868846665525334987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175325492983591108067559965 65747059868846665525334987)
      ·
        refine ⟨98620589803269998288002481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65747059868846665525334987 98620589803269998288002481)
        ·
          refine ⟨73965442352452498716001861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98620589803269998288002481 73965442352452498716001861)
          ·
            refine ⟨13868520441084843509250349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73965442352452498716001861 13868520441084843509250349)
            ·
              refine ⟨5200695165406816315968881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13868520441084843509250349 5200695165406816315968881)
              ·
                refine ⟨3900521374055112236976661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200695165406816315968881 3900521374055112236976661)
                ·
                  refine ⟨182836939408833386108281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3900521374055112236976661 182836939408833386108281)
                  ·
                    rfl

theorem cell23_3204663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 6].length) (baseStart_3204663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204663 prefixEnd_3204663 := by exact prefixLift 3204663
  have htrace : WordTrace (prefixWord ++ tailWord_3204663) baseStart_3204663 baseEnd_3204663 := by
    simpa [prefixWord, tailWord_3204663, baseEnd_3204663] using wordTrace_append hprefix tailTrace_3204663
  have hstable : (prefixWord ++ tailWord_3204663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204663).length < 2 ^ (prefixWord ++ tailWord_3204663).sum := by decide
  have hdescent : baseEnd_3204663 < baseStart_3204663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204666 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3204666 : Nat := 118140960795 + 3204666 * 2 ^ 59
def prefixEnd_3204666 : Nat := 4983230072969 + 3 ^ 40 * 3204666 * 2
def baseEnd_3204666 : Nat := 1645533995121463963237015

theorem tailTrace_3204666 : CollatzResearch.WordTrace tailWord_3204666 prefixEnd_3204666 1645533995121463963237015 := by
  unfold tailWord_3204666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29220942852012467556016463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77922514272033246816043901 29220942852012467556016463)
  ·
    refine ⟨43831414278018701334024695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29220942852012467556016463 43831414278018701334024695)
    ·
      refine ⟨65747121417028052001037043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43831414278018701334024695 65747121417028052001037043)
      ·
        refine ⟨98620682125542078001555565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65747121417028052001037043 98620682125542078001555565)
        ·
          refine ⟨36982755797078279250583337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98620682125542078001555565 36982755797078279250583337)
          ·
            refine ⟨27737066847808709437937503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36982755797078279250583337 27737066847808709437937503)
            ·
              refine ⟨41605600271713064156906255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27737066847808709437937503 41605600271713064156906255)
              ·
                refine ⟨62408400407569596235359383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41605600271713064156906255 62408400407569596235359383)
                ·
                  refine ⟨93612600611354394353039075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62408400407569596235359383 93612600611354394353039075)
                  ·
                    refine ⟨140418900917031591529558613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93612600611354394353039075 140418900917031591529558613)
                    ·
                      refine ⟨1645533995121463963237015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140418900917031591529558613 1645533995121463963237015)
                      ·
                        rfl

theorem cell23_3204666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3204666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204666 prefixEnd_3204666 := by exact prefixLift 3204666
  have htrace : WordTrace (prefixWord ++ tailWord_3204666) baseStart_3204666 baseEnd_3204666 := by
    simpa [prefixWord, tailWord_3204666, baseEnd_3204666] using wordTrace_append hprefix tailTrace_3204666
  have hstable : (prefixWord ++ tailWord_3204666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204666).length < 2 ^ (prefixWord ++ tailWord_3204666).sum := by decide
  have hdescent : baseEnd_3204666 < baseStart_3204666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204743 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3204743 : Nat := 118140960795 + 3204743 * 2 ^ 59
def prefixEnd_3204743 : Nat := 4983230072969 + 3 ^ 40 * 3204743 * 2
def baseEnd_3204743 : Nat := 1645573533131860161974161

theorem tailTrace_3204743 : CollatzResearch.WordTrace tailWord_3204743 prefixEnd_3204743 1645573533131860161974161 := by
  unfold tailWord_3204743
  simp only [CollatzResearch.WordTrace]
  refine ⟨116886579828770912374618883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77924386552513941583079255 116886579828770912374618883)
  ·
    refine ⟨175329869743156368561928325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116886579828770912374618883 175329869743156368561928325)
    ·
      refine ⟨32874350576841819105361561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175329869743156368561928325 32874350576841819105361561)
      ·
        refine ⟨24655762932631364329021171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32874350576841819105361561 24655762932631364329021171)
        ·
          refine ⟨36983644398947046493531757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24655762932631364329021171 36983644398947046493531757)
          ·
            refine ⟨13868866649605142435074409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36983644398947046493531757 13868866649605142435074409)
            ·
              refine ⟨10401649987203856826305807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13868866649605142435074409 10401649987203856826305807)
              ·
                refine ⟨15602474980805785239458711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401649987203856826305807 15602474980805785239458711)
                ·
                  refine ⟨23403712471208677859188067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15602474980805785239458711 23403712471208677859188067)
                  ·
                    refine ⟨35105568706813016788782101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23403712471208677859188067 35105568706813016788782101)
                    ·
                      refine ⟨1645573533131860161974161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35105568706813016788782101 1645573533131860161974161)
                      ·
                        rfl

theorem cell23_3204743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3204743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204743 prefixEnd_3204743 := by exact prefixLift 3204743
  have htrace : WordTrace (prefixWord ++ tailWord_3204743) baseStart_3204743 baseEnd_3204743 := by
    simpa [prefixWord, tailWord_3204743, baseEnd_3204743] using wordTrace_append hprefix tailTrace_3204743
  have hstable : (prefixWord ++ tailWord_3204743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204743).length < 2 ^ (prefixWord ++ tailWord_3204743).sum := by decide
  have hdescent : baseEnd_3204743 < baseStart_3204743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204744 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3204744 : Nat := 118140960795 + 3204744 * 2 ^ 59
def prefixEnd_3204744 : Nat := 4983230072969 + 3 ^ 40 * 3204744 * 2
def baseEnd_3204744 : Nat := 548524682204171552687219

theorem tailTrace_3204744 : CollatzResearch.WordTrace tailWord_3204744 prefixEnd_3204744 548524682204171552687219 := by
  unfold tailWord_3204744
  simp only [CollatzResearch.WordTrace]
  refine ⟨58443308150883644772702643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77924410867844859696936857 58443308150883644772702643)
  ·
    refine ⟨87664962226325467159053965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58443308150883644772702643 87664962226325467159053965)
    ·
      refine ⟨32874360834872050184645237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87664962226325467159053965 32874360834872050184645237)
      ·
        refine ⟨3081971328269254704810491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32874360834872050184645237 3081971328269254704810491)
        ·
          refine ⟨4622956992403882057215737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081971328269254704810491 4622956992403882057215737)
          ·
            refine ⟨3467217744302911542911803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4622956992403882057215737 3467217744302911542911803)
            ·
              refine ⟨5200826616454367314367705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467217744302911542911803 5200826616454367314367705)
              ·
                refine ⟨3900619962340775485775779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200826616454367314367705 3900619962340775485775779)
                ·
                  refine ⟨5850929943511163228663669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900619962340775485775779 5850929943511163228663669)
                  ·
                    refine ⟨548524682204171552687219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5850929943511163228663669 548524682204171552687219)
                    ·
                      rfl

theorem cell23_3204744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3204744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204744 prefixEnd_3204744 := by exact prefixLift 3204744
  have htrace : WordTrace (prefixWord ++ tailWord_3204744) baseStart_3204744 baseEnd_3204744 := by
    simpa [prefixWord, tailWord_3204744, baseEnd_3204744] using wordTrace_append hprefix tailTrace_3204744
  have hstable : (prefixWord ++ tailWord_3204744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204744).length < 2 ^ (prefixWord ++ tailWord_3204744).sum := by decide
  have hdescent : baseEnd_3204744 < baseStart_3204744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204760 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3204760 : Nat := 118140960795 + 3204760 * 2 ^ 59
def prefixEnd_3204760 : Nat := 4983230072969 + 3 ^ 40 * 3204760 * 2
def baseEnd_3204760 : Nat := 1645582262302986595461583

theorem tailTrace_3204760 : CollatzResearch.WordTrace tailWord_3204760 prefixEnd_3204760 1645582262302986595461583 := by
  unfold tailWord_3204760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58443599934854662138993867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77924799913139549518658489 58443599934854662138993867)
  ·
    refine ⟨87665399902281993208490801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58443599934854662138993867 87665399902281993208490801)
    ·
      refine ⟨65749049926711494906368101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87665399902281993208490801 65749049926711494906368101)
      ·
        refine ⟨12327946861258405294944019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65749049926711494906368101 12327946861258405294944019)
        ·
          refine ⟨18491920291887607942416029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12327946861258405294944019 18491920291887607942416029)
          ·
            refine ⟨6934470109457852978406011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18491920291887607942416029 6934470109457852978406011)
            ·
              refine ⟨10401705164186779467609017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934470109457852978406011 10401705164186779467609017)
              ·
                refine ⟨7801278873140084600706763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10401705164186779467609017 7801278873140084600706763)
                ·
                  refine ⟨11701918309710126901060145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801278873140084600706763 11701918309710126901060145)
                  ·
                    refine ⟨8776438732282595175795109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11701918309710126901060145 8776438732282595175795109)
                    ·
                      refine ⟨1645582262302986595461583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8776438732282595175795109 1645582262302986595461583)
                      ·
                        rfl

theorem cell23_3204760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3204760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204760 prefixEnd_3204760 := by exact prefixLift 3204760
  have htrace : WordTrace (prefixWord ++ tailWord_3204760) baseStart_3204760 baseEnd_3204760 := by
    simpa [prefixWord, tailWord_3204760, baseEnd_3204760] using wordTrace_append hprefix tailTrace_3204760
  have hstable : (prefixWord ++ tailWord_3204760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204760).length < 2 ^ (prefixWord ++ tailWord_3204760).sum := by decide
  have hdescent : baseEnd_3204760 < baseStart_3204760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204764 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3204764 : Nat := 118140960795 + 3204764 * 2 ^ 59
def prefixEnd_3204764 : Nat := 4983230072969 + 3 ^ 40 * 3204764 * 2
def baseEnd_3204764 : Nat := 1645584316225604579811565

theorem tailTrace_3204764 : CollatzResearch.WordTrace tailWord_3204764 prefixEnd_3204764 1645584316225604579811565 := by
  unfold tailWord_3204764
  simp only [CollatzResearch.WordTrace]
  refine ⟨58443672880847416480566673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77924897174463221974088897 58443672880847416480566673)
  ·
    refine ⟨43832754660635562360425005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58443672880847416480566673 43832754660635562360425005)
    ·
      refine ⟨16437282997738335885159377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43832754660635562360425005 16437282997738335885159377)
      ·
        refine ⟨12327962248303751913869533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16437282997738335885159377 12327962248303751913869533)
        ·
          refine ⟨4622985843113906967701075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12327962248303751913869533 4622985843113906967701075)
          ·
            refine ⟨6934478764670860451551613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4622985843113906967701075 6934478764670860451551613)
            ·
              refine ⟨2600429536751572669331855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6934478764670860451551613 2600429536751572669331855)
              ·
                refine ⟨3900644305127359003997783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600429536751572669331855 3900644305127359003997783)
                ·
                  refine ⟨5850966457691038505996675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900644305127359003997783 5850966457691038505996675)
                  ·
                    refine ⟨8776449686536557758995013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850966457691038505996675 8776449686536557758995013)
                    ·
                      refine ⟨1645584316225604579811565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8776449686536557758995013 1645584316225604579811565)
                      ·
                        rfl

theorem cell23_3204764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3204764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204764 prefixEnd_3204764 := by exact prefixLift 3204764
  have htrace : WordTrace (prefixWord ++ tailWord_3204764) baseStart_3204764 baseEnd_3204764 := by
    simpa [prefixWord, tailWord_3204764, baseEnd_3204764] using wordTrace_append hprefix tailTrace_3204764
  have hstable : (prefixWord ++ tailWord_3204764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204764).length < 2 ^ (prefixWord ++ tailWord_3204764).sum := by decide
  have hdescent : baseEnd_3204764 < baseStart_3204764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204770 : List Nat := [3, 3, 1, 4, 1, 11]
def baseStart_3204770 : Nat := 118140960795 + 3204770 * 2 ^ 59
def prefixEnd_3204770 : Nat := 4983230072969 + 3 ^ 40 * 3204770 * 2
def baseEnd_3204770 : Nat := 6771964597158566075459

theorem tailTrace_3204770 : CollatzResearch.WordTrace tailWord_3204770 prefixEnd_3204770 6771964597158566075459 := by
  unfold tailWord_3204770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29221891149918273996462941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77925043066448730657234509 29221891149918273996462941)
  ·
    refine ⟨10958209181219352748673603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29221891149918273996462941 10958209181219352748673603)
    ·
      refine ⟨16437313771829029123010405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10958209181219352748673603 16437313771829029123010405)
      ·
        refine ⟨3081996332217942960564451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16437313771829029123010405 3081996332217942960564451)
        ·
          refine ⟨4622994498326914440846677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081996332217942960564451 4622994498326914440846677)
          ·
            refine ⟨6771964597158566075459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4622994498326914440846677 6771964597158566075459)
            ·
              rfl

theorem cell23_3204770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 11].length) (baseStart_3204770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204770 prefixEnd_3204770 := by exact prefixLift 3204770
  have htrace : WordTrace (prefixWord ++ tailWord_3204770) baseStart_3204770 baseEnd_3204770 := by
    simpa [prefixWord, tailWord_3204770, baseEnd_3204770] using wordTrace_append hprefix tailTrace_3204770
  have hstable : (prefixWord ++ tailWord_3204770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204770).length < 2 ^ (prefixWord ++ tailWord_3204770).sum := by decide
  have hdescent : baseEnd_3204770 < baseStart_3204770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204781 : List Nat := [1, 5, 2, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3204781 : Nat := 118140960795 + 3204781 * 2 ^ 59
def prefixEnd_3204781 : Nat := 4983230072969 + 3 ^ 40 * 3204781 * 2
def baseEnd_3204781 : Nat := 1645593045396731013298987

theorem tailTrace_3204781 : CollatzResearch.WordTrace tailWord_3204781 prefixEnd_3204781 1645593045396731013298987 := by
  unfold tailWord_3204781
  simp only [CollatzResearch.WordTrace]
  refine ⟨116887965802633244864502197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77925310535088829909668131 116887965802633244864502197)
  ·
    refine ⟨10958246793996866706047081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116887965802633244864502197 10958246793996866706047081)
    ·
      refine ⟨8218685095497650029535311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10958246793996866706047081 8218685095497650029535311)
      ·
        refine ⟨12328027643246475044302967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8218685095497650029535311 12328027643246475044302967)
        ·
          refine ⟨18492041464869712566454451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12328027643246475044302967 18492041464869712566454451)
          ·
            refine ⟨27738062197304568849681677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492041464869712566454451 27738062197304568849681677)
            ·
              refine ⟨10401773323989213318630629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27738062197304568849681677 10401773323989213318630629)
              ·
                refine ⟨1950332498247977497243243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10401773323989213318630629 1950332498247977497243243)
                ·
                  refine ⟨2925498747371966245864865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950332498247977497243243 2925498747371966245864865)
                  ·
                    refine ⟨2194124060528974684398649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2925498747371966245864865 2194124060528974684398649)
                    ·
                      refine ⟨1645593045396731013298987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194124060528974684398649 1645593045396731013298987)
                      ·
                        rfl

theorem cell23_3204781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3204781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204781 prefixEnd_3204781 := by exact prefixLift 3204781
  have htrace : WordTrace (prefixWord ++ tailWord_3204781) baseStart_3204781 baseEnd_3204781 := by
    simpa [prefixWord, tailWord_3204781, baseEnd_3204781] using wordTrace_append hprefix tailTrace_3204781
  have hstable : (prefixWord ++ tailWord_3204781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204781).length < 2 ^ (prefixWord ++ tailWord_3204781).sum := by decide
  have hdescent : baseEnd_3204781 < baseStart_3204781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204797 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3204797 : Nat := 118140960795 + 3204797 * 2 ^ 59
def prefixEnd_3204797 : Nat := 4983230072969 + 3 ^ 40 * 3204797 * 2
def baseEnd_3204797 : Nat := 1645601261087202950698913

theorem tailTrace_3204797 : CollatzResearch.WordTrace tailWord_3204797 prefixEnd_3204797 1645601261087202950698913 := by
  unfold tailWord_3204797
  simp only [CollatzResearch.WordTrace]
  refine ⟨116888549370575279597084645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77925699580383519731389763 116888549370575279597084645)
  ·
    refine ⟨21916603006982864924453371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116888549370575279597084645 21916603006982864924453371)
    ·
      refine ⟨32874904510474297386680057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21916603006982864924453371 32874904510474297386680057)
      ·
        refine ⟨24656178382855723040010043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32874904510474297386680057 24656178382855723040010043)
        ·
          refine ⟨36984267574283584560015065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24656178382855723040010043 36984267574283584560015065)
          ·
            refine ⟨27738200680712688420011299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36984267574283584560015065 27738200680712688420011299)
            ·
              refine ⟨41607301021069032630016949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27738200680712688420011299 41607301021069032630016949)
              ·
                refine ⟨3900684470725221809064089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41607301021069032630016949 3900684470725221809064089)
                ·
                  refine ⟨2925513353043916356798067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3900684470725221809064089 2925513353043916356798067)
                  ·
                    refine ⟨4388270029565874535197101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2925513353043916356798067 4388270029565874535197101)
                    ·
                      refine ⟨1645601261087202950698913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4388270029565874535197101 1645601261087202950698913)
                      ·
                        rfl

theorem cell23_3204797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3204797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204797 prefixEnd_3204797 := by exact prefixLift 3204797
  have htrace : WordTrace (prefixWord ++ tailWord_3204797) baseStart_3204797 baseEnd_3204797 := by
    simpa [prefixWord, tailWord_3204797, baseEnd_3204797] using wordTrace_append hprefix tailTrace_3204797
  have hstable : (prefixWord ++ tailWord_3204797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204797).length < 2 ^ (prefixWord ++ tailWord_3204797).sum := by decide
  have hdescent : baseEnd_3204797 < baseStart_3204797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
